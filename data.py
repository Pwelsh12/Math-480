import csv
import torch
from torch.utils.data import Dataset, DataLoader, random_split
import torch.nn.functional as F
from torch import nn
import numpy as np

device = "cpu"

def parenthesization_to_tensor(parenthesization):
    
    # Calculate the length of the parenthesization string
    
    length = len(parenthesization)
    n = length // 2  # Calculate n from the length of the parenthesization string

    # Initialize a tensor of zeros with shape (length, 2)
    tensor = torch.zeros((length, 2), dtype=torch.int)

    # Map parenthesization characters to one-hot encoded vectors
    for i, char in enumerate(parenthesization):
        if char == '(':
            tensor[i][0] = 1
        elif char == ')':
            tensor[i][1] = 1
    flatten_tensor = tensor.flatten().float()
    
    return flatten_tensor


class ParenthesizationDataset(Dataset):
    def __init__(self, n):
        self.data = []
        filename = f"data/parenthesizations_{n}.csv"
        with open(filename, 'r') as file:
            csv_reader = csv.DictReader(file)
            for row in csv_reader:
                self.data.append((parenthesization_to_tensor(row["parenthesization"]), int(row["valid"])))

    def __len__(self):
        return len(self.data)

    def __getitem__(self, idx):
        return self.data[idx]

class ParenthesizationModel(nn.Module):
    def __init__(self, n):
        super().__init__()
        self.fc = nn.Linear(2*2*n, 2)

    def forward(self, x):
        return self.fc(x) 
    
