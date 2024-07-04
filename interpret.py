import matplotlib.pyplot as plt
import torch
from typing import List
from data import PAD_TOKEN, padding_mask
import numpy as np

def plot_linear_layer(layer):
    """
    Plots a heatmap of the weights for a linear layer.

    Parameters:
        layer (nn.Linear): The Linear layer for which the weights are to be visualized.
    """
    # Extract the weights from the layer and convert them to a NumPy array
    weights = layer.weight.cpu().detach().numpy()
    
    # Create the heatmap using matplotlib
    plt.figure(figsize=(10, 8))
    plt.imshow(weights, aspect='auto', cmap='viridis')
    plt.colorbar()
    plt.title(f'Heatmap of {layer.__class__.__name__} Weights')
    plt.xlabel('Output Neurons')
    plt.ylabel('Input Neurons')
    plt.show()


def incorrect_predictions(model: torch.nn.Module, dataloader: torch.utils.data.DataLoader) -> List[List[List[int]]]:
    """
    Given a model and a dataloader, this function evaluates the model by predicting the labels for each input in the dataloader.
    It keeps track of incorrect predictions and returns a list of inputs that were incorrectly predicted for each label.

    Args:
        model (torch.nn.Module): The model used for prediction.
        dataloader (torch.utils.data.DataLoader): The dataloader containing the input data.

    Returns:
        List[List[List[int]]]: A list of incorrect predictions for each label. The list contains two sublists, one for each label.
            Each sublist contains a list of inputs that were incorrectly predicted for that label.
            Each input is represented as a list of integers.
    """
    model.eval()  # Set the model to evaluation mode

    incorrect_predictions = [[], []]  # Initialize list for incorrect predictions for two labels
    total_parentheses = 0  # Initialize a counter for the total number of parentheses evaluated
    
    with torch.no_grad():  # Disable gradient calculation
        for inputs, labels in dataloader:
            outputs = model(inputs)  # Forward pass
            cls_outputs = outputs[:, 0, :]  # Assuming the CLS token is the first token in each sequence
            _, predicted = torch.max(cls_outputs, 1)  # Extract class indices from CLS token outputs

            # Debug: Print inputs, labels, and predictions
            #print(f"Inputs: {inputs.tolist()}")
            #print(f"Labels: {labels.tolist()}")
            #print(f"Predicted: {predicted.tolist()}")

            for input_tensor, label, prediction in zip(inputs, labels, predicted):
                input_list = input_tensor.tolist()
                num_parentheses = sum(1 for token in input_list if token == 0 or token == 1)
                total_parentheses += num_parentheses

                if prediction != label:  # If the prediction is incorrect
                    input_list = input_tensor.tolist()  # Convert tensor to list of integers
                    incorrect_predictions[label.item()].append(input_list)  # Append to the corresponding sublist

    print(f"Total number of parentheses evaluated: {total_parentheses}")
    return incorrect_predictions


def token_contributions(model, single_input):
    """
    Calculates the contributions of each token in the single_input sequence to each class in the model's predicted output. 
    The contribution of a single token is calculated as the difference between the model output with the given input and 
    the model output with the single token changed to the other parenthesis.

    Args:
        model (torch.nn.Module): The model used for prediction.
        single_input (torch.Tensor): The input sequence for which token contributions are calculated.

    Returns:
        List[float]: A list of contributions of each token to the model's output.
    """
    single_input = single_input.unsqueeze(0)  # Add batch dimension
    model.eval()  # Set the model to evaluation mode

    # Original output
    original_output = model(single_input, mask=padding_mask(single_input))
    original_output = original_output[:, 0, :]  # Get the CLS token output

    result = []

    with torch.no_grad():  # Disable gradient calculation
        for i in range(single_input.size(1)):
            if single_input[0, i] == 0:  # If the token is '(' (0)
                modified_input = single_input.clone()
                modified_input[0, i] = 1  # Change to ')' (1)
            elif single_input[0, i] == 1:  # If the token is ')' (1)
                modified_input = single_input.clone()
                modified_input[0, i] = 0  # Change to '(' (0)
            else:
                # If it's not a parenthesis token, contribution is 0
                #result
                continue

            # Modified output
            modified_output = model(modified_input, mask=padding_mask(modified_input))
            modified_output = modified_output[:, 0, :]  # Get the CLS token output

            # Contribution calculation
            contribution = (original_output - modified_output).squeeze().tolist()
            result.append(contribution)

    return result



def collect_activations(model, dataloader):
    """
    Returns the frequency of each hidden feature's activation in the feedforward layer of the model
    over all inputs in the dataloader.

    Args:
        model (torch.nn.Module): The model used for prediction.
        dataloader (torch.utils.data.DataLoader): The dataloader containing the input data.

    Returns:
        List[int]: A list of frequencies for each hidden feature in the feedforward layer of the model.
    """
    model.eval()  # Set the model to evaluation mode
    activation_counts = None

    with torch.no_grad():
        for inputs, _ in dataloader:
            #print("Processing inputs through the model.")
            model(inputs)  # Forward pass
            # Access activations directly from the custom layer
            activations_data = model.encoder.layers[0].activations
            if activations_data is not None:
                #print("Batch activations collected.")
                activations_data = np.array(activations_data)  # Ensure activations are numpy array
                
                binary_activations = (activations_data > 0).astype(int)  # Convert to binary
                if activation_counts is None:
                    activation_counts = binary_activations.sum(axis=0)
                else:
                    activation_counts += binary_activations.sum(axis=0)
            else:
                print("No activations collected for this batch.")

    if activation_counts is None:
        print("No activations were collected. Please check the model structure.")
        return []

    # Ensure activation_counts is an array before converting to list
    if isinstance(activation_counts, np.ndarray):
        result = activation_counts.tolist()
    else:
        print("activation_counts is not an array:", activation_counts)
        result = []

    print(f"Total number of activations collected: {len(result)}")
    print(f"Sample activations: {result[:10]}")  # Print the first 10 activation counts as a sample

    return result


