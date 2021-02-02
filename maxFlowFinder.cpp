#include <algorithm>
#include <cassert>
#include <iostream>
#include <list>
#include <queue>
#include <vector>

template <typename TFlow> struct Edge {
    unsigned int start, finish;
    TFlow capacity, flow;

    Edge(unsigned int start_, unsigned int finish_, TFlow capacity_, TFlow flow_)
        : start(start_), finish(finish_), capacity(capacity_), flow(flow_) {}

    TFlow getResidualCapacity() const { return capacity - flow; }

    int getStart() const { return start; }

    int getFinish() const { return finish; }
};

template <typename TFlow> class NetworkInterface {
  public:
    virtual unsigned int getGraphSize() const = 0;

    virtual unsigned int getSource() const = 0;

    virtual unsigned int getSink() const = 0;

    virtual TFlow getFlow() const = 0;

    virtual void addEdge(unsigned int start, unsigned int finish, TFlow capacity) = 0;

    // for (Iterator it = begin(v); it.isValid(); it.goNext())
    class IteratorInterface {
      public:
        virtual bool isValid() const = 0;

        virtual void goNext() = 0;

        virtual TFlow getCapacity() const = 0;

        virtual TFlow getResidualCapacity() const = 0;

        virtual TFlow getNeededResidualCapacity(bool isIncidentEdge = false) const = 0;

        virtual unsigned int getStart() const = 0;

        virtual unsigned int getFinish() const = 0;

        virtual void push(TFlow f) = 0;

        virtual bool isSaturated() const = 0;

        virtual Edge<TFlow> getEdge(bool isIncidentEdge = false) const = 0;
    };
};

template <typename TFlow = long long> class Network : public NetworkInterface<TFlow> {
  public:
    Network(unsigned int graphSize, unsigned int source, unsigned int sink)
        : graphSize_(graphSize), source_(source), sink_(sink), edges_(), begins_(graphSize, -1), nexts_() {}

    unsigned int getGraphSize() const override { return graphSize_; }

    unsigned int getSource() const override { return source_; }

    unsigned int getSink() const override { return sink_; }

    TFlow getFlow() const override {
        TFlow flow = 0;
        for (int i = begins_[source_]; i != -1; i = nexts_[i]) {
            flow += edges_[i].flow;
        }
        return flow;
    }

    void addEdge(unsigned int start, unsigned int finish, TFlow capacity) override {
        addEdgeLocal_(start, finish, capacity, TFlow(0));
        addEdgeLocal_(finish, start, TFlow(0), TFlow(0));
    }

    // for (Iterator it = begin(v); it.isValid(); it.goNext())
    class Iterator : public NetworkInterface<TFlow>::IteratorInterface {
      public:
        Iterator() : myNetwork_(nullptr), numEdge_(-1) {}

        explicit Iterator(Network *myNetwork, int numEdge) : myNetwork_(myNetwork), numEdge_(numEdge) {}

        bool isValid() const override { return numEdge_ != -1; }

        void goNext() override {
            if (!isValid()) {
                throw std::runtime_error("iterator reached the end at goNext()");
            }
            numEdge_ = myNetwork_->nexts_[numEdge_];
        }

        TFlow getCapacity() const override { return getEdge().capacity; }

        TFlow getResidualCapacity() const override { return getEdge().getResidualCapacity(); }

        TFlow getNeededResidualCapacity(bool isIncidentEdge = false) const override {
            return getEdge(isIncidentEdge).getResidualCapacity();
        }

        unsigned int getStart() const override { return getEdge().start; }

        unsigned int getFinish() const override { return getEdge().finish; }

        void push(TFlow f) override {
            if (!isValid()) {
                throw std::runtime_error("iterator reached the end at push()");
            }
            myNetwork_->push_(numEdge_, f);
        }

        bool isSaturated() const override {
            return myNetwork_->edges_[numEdge_].capacity == myNetwork_->edges_[numEdge_].flow;
        }

        Edge<TFlow> getEdge(bool isIncidentEdge = false) const override {
            if (!isValid()) {
                throw std::runtime_error("iterator reached the end at getEdge()");
            }
            return isIncidentEdge ? myNetwork_->edges_[getIncidentEdge_(numEdge_)] : myNetwork_->edges_[numEdge_];
        }

      private:
        Network *myNetwork_;
        int numEdge_;
    };

    Iterator begin(unsigned int v) { return Iterator(this, begins_[v]); }

  private:
    unsigned int graphSize_, source_, sink_;
    std::vector<Edge<TFlow>> edges_; // ind <-> ind^1
    std::vector<int> begins_, nexts_;

    static int getIncidentEdge_(int numEdge) { return numEdge ^ 1; }

    void push_(int numEdge, TFlow f) {
        edges_[numEdge].flow += f;
        edges_[getIncidentEdge_(numEdge)].flow -= f;
    }

    void addEdgeLocal_(unsigned int start, unsigned int finish, TFlow capacity, TFlow flow) {
        edges_.emplace_back(Edge<TFlow>{start, finish, capacity, flow});
        nexts_.push_back(begins_[start]);
        begins_[start] = edges_.size() - 1;
    }
};

template <typename TFlow> class BlockingFlowFinder {
  public:
    BlockingFlowFinder<TFlow>(Network<TFlow> *network) : network_(network) {}

    virtual TFlow getMaxFlow() = 0;

  protected:
    Network<TFlow> *network_;
    std::vector<int> distInLayeredNetwork_;
    std::vector<TFlow> inPotential_;
    std::vector<TFlow> outPotential_;
    std::vector<typename Network<TFlow>::Iterator> firstUnsaturatedEdgeForward_;
    std::vector<typename Network<TFlow>::Iterator> firstUnsaturatedEdgeBack_;
    std::vector<bool> isVertexRemoved_;

    void initFirstUnsaturatedEdge_() {
        firstUnsaturatedEdgeForward_.resize(network_->getGraphSize());
        firstUnsaturatedEdgeBack_.resize(network_->getGraphSize());
        for (unsigned int vertex = 0; vertex < network_->getGraphSize(); ++vertex) {
            firstUnsaturatedEdgeForward_[vertex] = network_->begin(vertex);
            firstUnsaturatedEdgeBack_[vertex] = network_->begin(vertex);
        }
    }

    TFlow getPotential_(unsigned int vertex) const { return std::min(inPotential_[vertex], outPotential_[vertex]); }

    int getVertexWithLeastNonZeroPotential_() const {
        int resultVertex = -1;
        for (unsigned int vertex = 0; vertex < network_->getGraphSize(); ++vertex) {
            if (!isVertexRemoved_[vertex] &&
                (resultVertex == -1 || getPotential_(vertex) < getPotential_(resultVertex))) {
                resultVertex = vertex;
            }
        }
        return resultVertex;
    }

    void removeVertexZeroPotential_() {
        std::queue<unsigned int> queue_;
        for (unsigned int vertex = 0; vertex < network_->getGraphSize(); ++vertex) {
            if (!isVertexRemoved_[vertex] && !getPotential_(vertex)) {
                isVertexRemoved_[vertex] = true;
                queue_.push(vertex);
            }
        }

        while (!queue_.empty()) {
            unsigned int vertex = queue_.front();
            queue_.pop();
            for (typename Network<TFlow>::Iterator edge = network_->begin(vertex); edge.isValid(); edge.goNext()) {
                unsigned edgeFinish = edge.getFinish();
                if (distInLayeredNetwork_[vertex] + 1 == distInLayeredNetwork_[edgeFinish]) {
                    inPotential_[edgeFinish] -= edge.getNeededResidualCapacity(false);
                }
                if (distInLayeredNetwork_[vertex] - 1 == distInLayeredNetwork_[edgeFinish]) {
                    outPotential_[edgeFinish] -= edge.getNeededResidualCapacity(true);
                }

                if (!getPotential_(edgeFinish) && !isVertexRemoved_[edgeFinish]) {
                    isVertexRemoved_[edgeFinish] = true;
                    queue_.push(edgeFinish);
                }
            }
        }
    }

    void pushFlowFromVertex_(unsigned int vertex, std::queue<unsigned int> &queue_, std::vector<TFlow> &pushedFlow,
                             std::vector<TFlow> &secondTypeOfPotential,
                             std::vector<typename Network<TFlow>::Iterator> &directioNiterators, int need,
                             TFlow multiplier) {
        while (pushedFlow[vertex]) {
            typename Network<TFlow>::Iterator edge = directioNiterators[vertex];
            unsigned int edgeFinish = edge.getFinish();
            if (distInLayeredNetwork_[vertex] + multiplier == distInLayeredNetwork_[edgeFinish] &&
                !isVertexRemoved_[edgeFinish]) {
                if (edge.getNeededResidualCapacity(need)) {
                    TFlow minOfPushedFlowAndResidualCapacity =
                        std::min(pushedFlow[vertex], edge.getNeededResidualCapacity(need));

                    pushedFlow[vertex] -= minOfPushedFlowAndResidualCapacity;
                    if (!pushedFlow[edgeFinish]) {
                        queue_.push(edgeFinish);
                    }
                    pushedFlow[edgeFinish] += minOfPushedFlowAndResidualCapacity;

                    edge.push(multiplier * minOfPushedFlowAndResidualCapacity);

                    secondTypeOfPotential[edgeFinish] -= minOfPushedFlowAndResidualCapacity;
                }
            }
            if (pushedFlow[vertex]) {
                directioNiterators[vertex].goNext();
            }
        }
    }

    void initPotentials_() {
        inPotential_.assign(network_->getGraphSize(), TFlow(0));
        outPotential_.assign(network_->getGraphSize(), TFlow(0));
        for (unsigned int vertex = 0; vertex < network_->getGraphSize(); ++vertex) {
            for (typename Network<TFlow>::Iterator edge = network_->begin(vertex); edge.isValid(); edge.goNext()) {
                if (distInLayeredNetwork_[vertex] + 1 == distInLayeredNetwork_[edge.getFinish()]) {
                    inPotential_[edge.getFinish()] += edge.getResidualCapacity();
                    outPotential_[vertex] += edge.getResidualCapacity();
                }
            }
        }
        inPotential_[network_->getSource()] = outPotential_[network_->getSource()];
        outPotential_[network_->getSink()] = inPotential_[network_->getSink()];
    }

    void push_(unsigned int startVertex, unsigned int finishVertex, TFlow potentialOfStartVertex,
               std::vector<TFlow> &firstTypeOfPotential, std::vector<TFlow> &secondTypeOfPotential,
               std::vector<typename Network<TFlow>::Iterator> &directioNiterators, int need, TFlow multiplier) {

        std::queue<unsigned int> queue_;
        queue_.push(startVertex);
        std::vector<TFlow> pushedFlow(network_->getGraphSize(), TFlow(0));
        pushedFlow[startVertex] += potentialOfStartVertex;
        while (queue_.front() != finishVertex) {
            unsigned int vertex = queue_.front();
            queue_.pop();

            firstTypeOfPotential[vertex] -= pushedFlow[vertex];
            pushFlowFromVertex_(vertex, queue_, pushedFlow, secondTypeOfPotential, directioNiterators, need,
                                multiplier);
        }
    }

    void findBlockingFlow() {
        initPotentials_();
        isVertexRemoved_.assign(network_->getGraphSize(), false);
        removeVertexZeroPotential_();
        initFirstUnsaturatedEdge_();
        int vertex = getVertexWithLeastNonZeroPotential_();
        while (vertex != -1) {
            TFlow potentialOfStartVertex = getPotential_(vertex);
            push_(vertex, network_->getSink(), potentialOfStartVertex, outPotential_, inPotential_,
                  firstUnsaturatedEdgeForward_, 0, TFlow(1));
            push_(vertex, network_->getSource(), potentialOfStartVertex, inPotential_, outPotential_,
                  firstUnsaturatedEdgeBack_, 1, TFlow(-1));

            removeVertexZeroPotential_();

            vertex = getVertexWithLeastNonZeroPotential_();
        }
    }
};

template <typename TFlow> class MKMSolver : public BlockingFlowFinder<TFlow> {
  public:
    MKMSolver(Network<TFlow> *network) : BlockingFlowFinder<TFlow>(network){};
    ~MKMSolver() = default;

    TFlow getMaxFlow() override {
        bfs_();
        while (distInLayeredNetwork_[network_->getSink()] != numberOfUnvisitedVertex) {
            this->findBlockingFlow();
            bfs_();
        }

        return network_->getFlow();
    }

  private:
    using BlockingFlowFinder<TFlow>::network_;
    using BlockingFlowFinder<TFlow>::distInLayeredNetwork_;
    int numberOfUnvisitedVertex = -2;
    // numberOfUnvisitedVertex cant be 1, because i use this conditional "distInLayeredNetwork_[vertex] + 1 ==
    // distInLayeredNetwork_[edge.getFinish()]" in the program, and it doesn't work with numberOfUnvisitedVertex = -1,
    // but works with numberOfUnvisitedVertex <= -2

    void bfs_() {
        distInLayeredNetwork_.assign(network_->getGraphSize(), numberOfUnvisitedVertex);

        std::queue<unsigned int> queue_;
        queue_.push(network_->getSource());
        distInLayeredNetwork_[network_->getSource()] = 0;

        while (!queue_.empty()) {
            unsigned int vertex = queue_.front();
            queue_.pop();
            for (typename Network<TFlow>::Iterator edge = network_->begin(vertex); edge.isValid(); edge.goNext()) {
                unsigned int edgeFinish = edge.getFinish();
                if (distInLayeredNetwork_[edgeFinish] == numberOfUnvisitedVertex && edge.getResidualCapacity()) {
                    distInLayeredNetwork_[edgeFinish] = distInLayeredNetwork_[vertex] + 1;
                    queue_.push(edgeFinish);
                }
            }
        }

        for (unsigned int vertex = 0; vertex < network_->getGraphSize(); ++vertex) {
            if (distInLayeredNetwork_[vertex] > distInLayeredNetwork_[network_->getSink()]) {
                distInLayeredNetwork_[vertex] = numberOfUnvisitedVertex;
            }
        }
    }
};

template <typename TFlow> class PushRelabelFinder {
  public:
    PushRelabelFinder<TFlow>(Network<TFlow> *network) : network_(network) {}

    virtual TFlow getMaxFlow() = 0;

  protected:
    Network<TFlow> *network_;
    std::vector<TFlow> overflow_;
    std::vector<unsigned int> heights_;

    virtual void push_(typename Network<TFlow>::Iterator edge) {
        TFlow pushedFlow = std::min(overflow_[edge.getStart()], edge.getResidualCapacity());

        edge.push(pushedFlow);
        overflow_[edge.getStart()] -= pushedFlow;
        overflow_[edge.getFinish()] += pushedFlow;
    }

    virtual void releable_(unsigned int vertex) {
        unsigned int newHeight = heights_[vertex];

        for (typename Network<TFlow>::Iterator edge = network_->begin(vertex); edge.isValid(); edge.goNext()) {
            if (!edge.isSaturated()) {
                newHeight = std::min(newHeight, heights_[edge.getFinish()]);
            }
        }

        heights_[vertex] = newHeight + 1;
    }
};

template <typename TFlow> class GoldbergSolver : public PushRelabelFinder<TFlow> {
  public:
    GoldbergSolver(Network<TFlow> *network) : PushRelabelFinder<TFlow>(network){};
    ~GoldbergSolver() = default;

    TFlow getMaxFlow() override {
        init_();

        auto it = list_.begin();
        while (it != list_.end()) {
            unsigned int vertex = *it;

            if (discharge_(vertex)) {
                list_.erase(it);
                list_.push_front(vertex);
                it = list_.begin();
            }
            ++it;
        }

        return -overflow_[network_->getSource()];
    }

  private:
    using PushRelabelFinder<TFlow>::network_;
    using PushRelabelFinder<TFlow>::heights_;
    using PushRelabelFinder<TFlow>::overflow_;
    std::list<unsigned int> list_;

    void init_() {
        heights_.assign(network_->getGraphSize(), 0);
        overflow_.assign(network_->getGraphSize(), TFlow(0));
        unsigned int source = network_->getSource();

        for (typename Network<TFlow>::Iterator edgeFromSource = network_->begin(source); edgeFromSource.isValid();
             edgeFromSource.goNext()) {
            TFlow capacity = edgeFromSource.getCapacity();
            edgeFromSource.push(capacity);
            overflow_[source] -= capacity;
            overflow_[edgeFromSource.getFinish()] += capacity;
        }

        heights_[source] = network_->getGraphSize();

        for (unsigned int vertex = 0; vertex < network_->getGraphSize(); ++vertex) {
            if (vertex != source && vertex != network_->getSink()) {
                list_.push_back(vertex);
            }
        }
    }

    bool discharge_(unsigned int vertex) {
        typename Network<TFlow>::Iterator edge = network_->begin(vertex);
        bool hasHeightChanged = false;

        while (overflow_[vertex]) {
            if (!edge.isValid()) {
                hasHeightChanged = true;
                this->releable_(vertex);
                edge = network_->begin(vertex);
            } else if (!edge.isSaturated() && heights_[vertex] == 1 + heights_[edge.getFinish()]) {
                this->push_(edge);
            } else {
                edge.goNext();
            }
        }

        return hasHeightChanged;
    }
};
