import torch.nn
from torch import no_grad, stack
from torch.utils.data import DataLoader
from torch.nn import Module


"""
Functions you should use.
Please avoid importing any other torch functions or modules.
Your code will not pass if the gradescope autograder detects any changed imports
"""
from torch.nn import Parameter, Linear
from torch import optim, tensor, tensordot, empty, ones
from torch.nn.functional import cross_entropy, relu, mse_loss
from torch import movedim


class PerceptronModel(Module):
    def __init__(self, dimensions):
        """
        Initialize a new Perceptron instance.

        A perceptron classifies data points as either belonging to a particular
        class (+1) or not (-1). `dimensions` is the dimensionality of the data.
        For example, dimensions=2 would mean that the perceptron must classify
        2D points.

        In order for our autograder to detect your weight, initialize it as a 
        pytorch Parameter object as follows:

        Parameter(weight_vector)

        where weight_vector is a pytorch Tensor of dimension 'dimensions'

        
        Hint: You can use ones(dim) to create a tensor of dimension dim.
        """
        super(PerceptronModel, self).__init__()
        
        "*** YOUR CODE HERE ***"
        # self.w = None #Initialize your weights here
        weight_vector = ones(1,dimensions)
        self.w = Parameter(weight_vector)

    def get_weights(self):
        """
        Return a Parameter instance with the current weights of the perceptron.
        """
        return self.w

    def run(self, x):
        """
        Calculates the score assigned by the perceptron to a data point x.

        Inputs:
            x: a node with shape (1 x dimensions)
        Returns: a node containing a single number (the score)

        The pytorch function `tensordot` may be helpful here.
        """
        "*** YOUR CODE HERE ***"
        return tensordot(x, self.get_weights())

    def get_prediction(self, x):
        """
        Calculates the predicted class for a single data point `x`.

        Returns: 1 or -1
        """
        "*** YOUR CODE HERE ***"
        return 1 if self.run(x) >= 0 else -1


    def train(self, dataset):
        """
        Train the perceptron until convergence.
        You can iterate through DataLoader in order to 
        retrieve all the batches you need to train on.

        Each sample in the dataloader is in the form {'x': features, 'label': label} where label
        is the item we need to predict based off of its features.
        """        
        with no_grad():
            dataloader = DataLoader(dataset, batch_size=1, shuffle=True)
            "*** YOUR CODE HERE ***"

            while 1:
                success = 0
                for data in dataloader:
                    x, label = data['x'], data['label']
                    x_pred = self.get_prediction(x)
                    if x_pred != label:
                        self.w += label*x
                    else:
                        success += 1
                accuracy = success/dataloader.__len__()
                if accuracy == 1:
                    break


class RegressionModel(Module):
    """
    A neural network model for approximating a function that maps from real
    numbers to real numbers. The network should be sufficiently large to be able
    to approximate sin(x) on the interval [-2pi, 2pi] to reasonable precision.
    """
    def __init__(self):
        # Initialize your model parameters here
        "*** YOUR CODE HERE ***"
        super(RegressionModel, self).__init__()
        self.linear1 = Linear(1, 500)
        self.linear2 = Linear(500, 500)
        self.linear3 = Linear(500, 1)

    def forward(self, x):
        """
        Runs the model for a batch of examples.

        Inputs:
            x: a node with shape (batch_size x 1)
        Returns:
            A node with shape (batch_size x 1) containing predicted y-values
        """
        "*** YOUR CODE HERE ***"
        y1 = relu(self.linear1(x))
        y2 = relu(self.linear2(y1))
        y = self.linear3(y2)
        return y
    
    def get_loss(self, x, y):
        """
        Computes the loss for a batch of examples.

        Inputs:
            x: a node with shape (batch_size x 1)
            y: a node with shape (batch_size x 1), containing the true y-values
                to be used for training
        Returns: a tensor of size 1 containing the loss
        """
        "*** YOUR CODE HERE ***"
        pred = self.forward(x)
        loss = mse_loss(pred, y)

        return loss
  

    def train(self, dataset):
        """
        Trains the model.

        In order to create batches, create a DataLoader object and pass in `dataset` as well as your required 
        batch size. You can look at PerceptronModel as a guideline for how you should implement the DataLoader

        Each sample in the dataloader object will be in the form {'x': features, 'label': label} where label
        is the item we need to predict based off of its features.

        Inputs:
            dataset: a PyTorch dataset object containing data to be trained on
            
        """

        #your version
        "*** YOUR CODE HERE ***"
        dataloader = DataLoader(dataset, batch_size=128, shuffle=True)
        # model = RegressionModel()
        optimizer = optim.Adam(RegressionModel.parameters(self), lr=0.0001)
        # Loss = torch.nn.MSELoss()
        # with no_grad():
        epoch = 0
        loss = 0
        for i in range(2000):
            epoch_loss = 0
            for data in dataloader:
                x, label = data['x'], data['label']
                # y_pred = model(x)
                # loss = Loss(y_pred,label)
                optimizer.zero_grad()

                loss = self.get_loss(x, label)
                # print(epoch, loss.item())

                loss.backward()
                optimizer.step()
            epoch += 1
            epoch_loss = self.get_loss(dataset[:]['x'],dataset[:]['label'])
            print(epoch,epoch_loss.item())
            if(epoch_loss < 0.015):
                break





class DigitClassificationModel(Module):
    """
    A model for handwritten digit classification using the MNIST dataset.

    Each handwritten digit is a 28x28 pixel grayscale image, which is flattened
    into a 784-dimensional vector for the purposes of this model. Each entry in
    the vector is a floating point number between 0 and 1.

    The goal is to sort each digit into one of 10 classes (number 0 through 9).

    (See RegressionModel for more information about the APIs of different
    methods here. We recommend that you implement the RegressionModel before
    working on this part of the project.)
    """
    def __init__(self):
        # Initialize your model parameters here
        super().__init__()
        input_size = 28 * 28
        output_size = 10
        "*** YOUR CODE HERE ***"
        self.fc1 = Linear(input_size, 500)
        self.fc2 = Linear(500,300)
        self.fc3 = Linear(300,100)
        self.output = Linear(100, output_size)

    def run(self, x):
        """
        Runs the model for a batch of examples.

        Your model should predict a node with shape (batch_size x 10),
        containing scores. Higher scores correspond to greater probability of
        the image belonging to a particular class.

        Inputs:
            x: a tensor with shape (batch_size x 784)
        Output:
            A node with shape (batch_size x 10) containing predicted scores
                (also called logits)
        """
        """ YOUR CODE HERE """
        y1 = relu(self.fc1(x))
        y2 = relu(self.fc2(y1))
        y3 = relu(self.fc3(y2))

        y = self.output(y3)
        return y
    def get_loss(self, x, y):
        """
        Computes the loss for a batch of examples.

        The correct labels `y` are represented as a tensor with shape
        (batch_size x 10). Each row is a one-hot vector encoding the correct
        digit class (0-9).

        Inputs:
            x: a node with shape (batch_size x 784)
            y: a node with shape (batch_size x 10)
        Returns: a loss tensor
        """
        """ YOUR CODE HERE """
        y_pred = self.run(x)
        loss = cross_entropy(y_pred, y)
        return loss
        

    def train(self, dataset):
        """
        Trains the model.
        """
        """ YOUR CODE HERE """
        dataloader = DataLoader(dataset, batch_size=128, shuffle=True)

        # model = DigitClassificationModel()
        optimizer = optim.Adam(self.parameters(), lr=0.001)
        epoch = 0
        # loss = 0
        for i in range(5000):
            # epoch_loss = 0
            for data in dataloader:
                x, label = data['x'], data['label']
                loss = self.get_loss(x, label)
                # print(epoch, loss.item())

                optimizer.zero_grad()
                loss.backward()
                optimizer.step()
            epoch += 1
            validation_accuracy = dataset.get_validation_accuracy()
            print(epoch, validation_accuracy)
            if validation_accuracy > 0.98:
                break


class LanguageIDModel(Module):
    """
    A model for language identification at a single-word granularity.

    (See RegressionModel for more information about the APIs of different
    methods here. We recommend that you implement the RegressionModel before
    working on this part of the project.)
    """
    def __init__(self):
        # Our dataset contains words from five different languages, and the
        # combined alphabets of the five languages contain a total of 47 unique
        # characters.
        # You can refer to self.num_chars or len(self.languages) in your code
        self.num_chars = 47
        self.languages = ["English", "Spanish", "Finnish", "Dutch", "Polish"]
        super(LanguageIDModel, self).__init__()
        "*** YOUR CODE HERE ***"
        self.num_hiddenlayers = 300
        # Initialize your model parameters here
        h = self.num_hiddenlayers
        self.initial = Linear(self.num_chars,h)
        self.f = Linear(h, h)
        self.output = Linear(h,len(self.languages))

    def run(self, xs):
        """
        Runs the model for a batch of examples.

        Although words have different lengths, our data processing guarantees
        that within a single batch, all words will be of the same length (L).

        Here `xs` will be a list of length L. Each element of `xs` will be a
        tensor with shape (batch_size x self.num_chars), where every row in the
        array is a one-hot vector encoding of a character. For example, if we
        have a batch of 8 three-letter words where the last word is "cat", then
        xs[1] will be a tensor that contains a 1 at position (7, 0). Here the
        index 7 reflects the fact that "cat" is the last word in the batch, and
        the index 0 reflects the fact that the letter "a" is the inital (0th)
        letter of our combined alphabet for this task.

        Your model should use a Recurrent Neural Network to summarize the list
        `xs` into a single tensor of shape (batch_size x hidden_size), for your
        choice of hidden_size. It should then calculate a tensor of shape
        (batch_size x 5) containing scores, where higher scores correspond to
        greater probability of the word originating from a particular language.

        Inputs:
            xs: a list with L elements (one per character), where each element
                is a node with shape (batch_size x self.num_chars)
        Returns:
            A node with shape (batch_size x 5) containing predicted scores
                (also called logits)
        """
        "*** YOUR CODE HERE ***"

        # print("shape of xs = ", xs.shape)
        # print(xs[0],len(xs))
        # L = len(xs)
        h1 = self.initial(xs[0])
        L = xs.shape[0]
        # last_hi = h1
        hi = h1
        for i in range(1,L):
            # print(xs[i])
            print(xs[i].shape)
            hinitial = self.initial(xs[i])
            hi = relu(self.f(hi+hinitial))
            # last_hi = hi
        output = self.output(hi)
        return output

    
    def get_loss(self, xs, y):
        """
        Computes the loss for a batch of examples.

        The correct labels `y` are represented as a node with shape
        (batch_size x 5). Each row is a one-hot vector encoding the correct
        language.

        Inputs:
            xs: a list with L elements (one per character), where each element
                is a node with shape (batch_size x self.num_chars)
            y: a node with shape (batch_size x 5)
        Returns: a loss node
        """
        "*** YOUR CODE HERE ***"
        y_pred = self.run(xs)
        loss = mse_loss(y_pred, y)
        return loss

    def train(self, dataset):
        """
        Trains the model.

        Note that when you iterate through dataloader, each batch will returned as its own vector in the form
        (batch_size x length of word x self.num_chars). However, in order to run multiple samples at the same time,
        get_loss() and run() expect each batch to be in the form (length of word x batch_size x self.num_chars), meaning
        that you need to switch the first two dimensions of every batch. This can be done with the movedim() function 
        as follows:

        movedim(input_vector, initial_dimension_position, final_dimension_position)

        For more information, look at the pytorch documentation of torch.movedim()
        """
        "*** YOUR CODE HERE ***"
        dataloader = DataLoader(dataset, batch_size=128, shuffle=True)
        optimizer = optim.Adam(self.parameters(), lr=0.001)
        epoch = 0

        for i in range(5000):
            # epoch_loss = 0
            for data in dataloader:
                # print(data)
                x, label = data['x'], data['label']
                # print("aaaaaaaaaaaaaaaaa:", label)
                x = movedim(x, 1, 0)
                loss = self.get_loss(x, label)
                # print(i,loss.item())
                optimizer.zero_grad()
                loss.backward()
                optimizer.step()
            epoch += 1
            validation_accuracy = dataset.get_validation_accuracy()
            print(epoch, validation_accuracy)
            if validation_accuracy > 0.85:
                break


def Convolve(input: tensor, weight: tensor):
    """
    Acts as a convolution layer by applying a 2d convolution with the given inputs and weights.
    DO NOT import any pytorch methods to directly do this, the convolution must be done with only the functions
    already imported.

    There are multiple ways to complete this function. One possible solution would be to use 'tensordot'.
    If you would like to index a tensor, you can do it as such:

    tensor[y:y+height, x:x+width]

    This returns a subtensor who's first element is tensor[y,x] and has height 'height, and width 'width'
    """
    input_tensor_dimensions = input.shape
    weight_dimensions = weight.shape
    # Output_Tensor = tensor(())
    "*** YOUR CODE HERE ***"
    height = weight_dimensions[0]
    width = weight_dimensions[1]
    output_height = input.shape[0] - height + 1
    output_width = input.shape[1] - width + 1

    Output_Tensor = empty((output_height, output_width))
    cnt = 0
    for i in range(input_tensor_dimensions[0]-height+1):
        for j in range(input_tensor_dimensions[1]-width+1):
            source_matrix = input[i:i+height, j:j+width]
            # print(tensordot(source_matrix, weight))
            Output_Tensor[i, j] = tensordot(source_matrix, weight)
            cnt += 1

    "*** End Code ***"
    return Output_Tensor



class DigitConvolutionalModel(Module):
    """
    A model for handwritten digit classification using the MNIST dataset.

    This class is a convolutational model which has already been trained on MNIST.
    if Convolve() has been correctly implemented, this model should be able to achieve a high accuracy
    on the mnist dataset given the pretrained weights.


    """
    

    def __init__(self):
        # Initialize your model parameters here
        super().__init__()
        output_size = 10

        self.convolution_weights = Parameter(ones((3, 3)))
        """ YOUR CODE HERE """
        self.linear1 = Linear(26*26,500)
        self.linear2 = Linear(500, 200)
        self.output = Linear(200, output_size)

    def run(self, x):
        """
        The convolutional layer is already applied, and the output is flattened for you. You should treat x as
        a regular 1-dimentional datapoint now, similar to the previous questions.
        """
        x = x.reshape(len(x), 28, 28)
        x = stack(list(map(lambda sample: Convolve(sample, self.convolution_weights), x)))
        x = x.flatten(start_dim=1)
        """ YOUR CODE HERE """
        y1 = relu(self.linear1(x))
        y2 = relu(self.linear2(y1))
        output = self.output(y2)
        return output

    def get_loss(self, x, y):
        """
        Computes the loss for a batch of examples.

        The correct labels `y` are represented as a tensor with shape
        (batch_size x 10). Each row is a one-hot vector encoding the correct
        digit class (0-9).

        Inputs:
            x: a node with shape (batch_size x 784)
            y: a node with shape (batch_size x 10)
        Returns: a loss tensor
        """
        """ YOUR CODE HERE """
        pred = self.run(x)
        loss = mse_loss(pred, y)
        return loss
        

    def train(self, dataset):
        """
        Trains the model.
        """
        """ YOUR CODE HERE """
        dataloader = DataLoader(dataset, batch_size=128, shuffle=True)
        optimizer = optim.Adam(self.parameters(), lr=0.001)
        epoch = 0

        for i in range(5000):
            for data in dataloader:
                x, label = data['x'], data['label']
                loss = self.get_loss(x, label)
                # print(i,loss.item())
                optimizer.zero_grad()
                loss.backward()
                optimizer.step()
            epoch += 1
            validation_accuracy = dataset.get_validation_accuracy()
            print(epoch, validation_accuracy)
            if validation_accuracy > 0.81:
                break