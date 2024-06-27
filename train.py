import torch
from torch.utils.data import Dataset, DataLoader
import torch.nn as nn
import torch.optim as optim
import importlib
import random
import os
import csv
import data
import numpy as np

# Training and evaluation
def train_one_epoch(training_loader, model, loss_fn, optimizer):
    model.train()
    total_loss = 0.0
    for batch in training_loader:
        inputs, targets = batch
        optimizer.zero_grad()
        outputs = model(inputs)
        loss = loss_fn(outputs, targets)
        loss.backward()
        optimizer.step()
        total_loss += loss.item()
    return total_loss

def evaluate_model(model, test_loader):
    model.eval()
    confusion_matrix = [[0, 0], [0, 0]]
    with torch.no_grad():
        for batch in test_loader:
            inputs, targets = batch
            
            output = model(inputs)
            prediction = output.argmax(dim=1)
            for t, p in zip(targets.view(-1), prediction.view(-1)):
                confusion_matrix[t.long()][p.long()] += 1
    return confusion_matrix


def analyze_confusion_matrix(confusion_matrix):
    # Convert confusion matrix to a numpy array for easier calculations
    
        confusion_matrix = np.array(confusion_matrix)
    
    # Accuracy within each class
        class_accuracy = confusion_matrix.diagonal() / confusion_matrix.sum(axis=1)
    
    # Size of each class (total number of samples predicted for each class)
        class_size = confusion_matrix.sum(axis=1)
    
    # Overall accuracy
        overall_accuracy = confusion_matrix.diagonal().sum() / confusion_matrix.sum()
    
        return class_accuracy, class_size, overall_accuracy

       