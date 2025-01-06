
"""
Functions you should use.
Please avoid importing any other torch functions or modules.
Your code will not pass if the gradescope autograder detects any changed imports
"""

from torch.nn import Module
from torch.nn import Linear
from torch import tensor, double, optim
from torch.nn.functional import relu, mse_loss



class DeepQNetwork(Module):
    """
    A model that uses a Deep Q-value Network (DQN) to approximate Q(s,a) as part
    of reinforcement learning.
    """
    def __init__(self, state_dim, action_dim):
        self.num_actions = action_dim
        self.state_size = state_dim
        super(DeepQNetwork, self).__init__()
        # Remember to set self.learning_rate, self.numTrainingGames,
        # and self.batch_size!
        "*** YOUR CODE HERE ***"
        self.learning_rate = 0.2
        self.numTrainingGames = 5000
        self.batch_size = 200

        self.linear1 = Linear(self.state_size, 500).double()
        self.linear2 = Linear(500, 300).double()
        self.output = Linear(300, self.num_actions).double()
        self.optimizer = optim.SGD(self.parameters(), lr=self.learning_rate)
        "**END CODE"""
        self.double()


    def get_loss(self, states, Q_target):
        """
        Returns the Squared Loss between Q values currently predicted 
        by the network, and Q_target.
        Inputs:
            states: a (batch_size x state_dim) numpy array
            Q_target: a (batch_size x num_actions) numpy array, or None
        Output:
            loss node between Q predictions and Q_target
        """
        "*** YOUR CODE HERE ***"
        states = tensor(states, dtype=double)
        Q_target = tensor(Q_target, dtype=double)
        pred = self.run(states)
        loss = mse_loss(pred, Q_target)
        return loss

    def forward(self, states):
        """
        Runs the DQN for a batch of states.
        The DQN takes the state and returns the Q-values for all possible actions
        that can be taken. That is, if there are two actions, the network takes
        as input the state s and computes the vector [Q(s, a_1), Q(s, a_2)]
        Inputs:
            states: a (batch_size x state_dim) numpy array
            Q_target: a (batch_size x num_actions) numpy array, or None
        Output:
            result: (batch_size x num_actions) numpy array of Q-value
                scores, for each of the actions
        """
        "*** YOUR CODE HERE ***"
        states = tensor(states, dtype=double)

        y1 = relu(self.linear1(states))
        y2 = relu(self.linear2(y1))
        # y3 = relu(self.linear2(y2))
        y = self.output(y2)
        return y
    
    def run(self, states):
        return self.forward(states)

    def gradient_update(self, states, Q_target):
        """
        Update your parameters by one gradient step with the .update(...) function.
        You can look at the ML project for an idea of how to do this, but note that rather
        than iterating through a dataset, you should only be applying a single gradient step
        to the given datapoints.

        Inputs:
            states: a (batch_size x state_dim) numpy array
            Q_target: a (batch_size x num_actions) numpy array, or None
        Output:
            None
        """
        "*** YOUR CODE HERE ***"
        states = tensor(states, dtype=double)
        Q_target = tensor(Q_target, dtype=double)

        # optimizer = optim.SGD(self.parameters(), lr=self.learning_rate)
        # for i in range(self.numTrainingGames):
        loss = self.get_loss(states, Q_target)
        # print(loss)
        self.optimizer.zero_grad()
        loss.backward()
        self.optimizer.step()
