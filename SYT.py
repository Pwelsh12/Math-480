import itertools
import random
def is_valid_SYT(candidate):
    """
    Check if the given candidate tableau is a valid standard Young tableau.

    Parameters:
    - candidate (Tuple[Tuple[int]]): The tableau to be checked.

    Returns:
    - bool: True if the matrix is valid, False otherwise.
    """
    num_rows = len(candidate)
    
    # Check for strictly increasing rows
    for row in candidate:
        if any(row[i] >= row[i + 1] for i in range(len(row) - 1)):
            return False

    # Check for strictly increasing columns
    num_cols = max(len(row) for row in candidate)
    for col in range(num_cols):
        col_values = []
        for row in candidate:
            if col < len(row):
                col_values.append(row[col])
        if any(col_values[i] >= col_values[i + 1] for i in range(len(col_values) - 1)):
            return False

    return True

# Example usage
#print(is_valid_SYT(((1, 2, 3), (4, 5, 6), (7, 8, 9))))  # True
#print(is_valid_SYT(((1, 2, 3), (5, 4), (6))))           # False
#print(is_valid_SYT(((1, 2), (3, 4))))                   # True
#print(is_valid_SYT(((1, 3), (4, 2)))) 

def reshape_perm(perm, shape):
    """
    Reshapes a permutation into a tableau based on the given shape.

    Parameters:
    - perm (Tuple[int]): The permutation to be reshaped.
    - shape (Tuple[int]): The shape of the resulting tableau as a weakly decreasing tuple of integers.

    Returns:
    - Tuple[Tuple[int]]: A tuple of tuples representing the reshaped permutation as a tableau.

    Example:
    >>> reshape_perm((1, 2, 3, 4, 5, 6), (3, 2, 1))
    ((1, 2, 3), (4, 5), (6,))
    """
    result = []
    index = 0
    for length in shape:
        row = perm[index:index + length]
        result.append(tuple(row))
        index += length
    return tuple(result)

# Example usage
#print(reshape_perm((1, 2, 3, 4, 5, 6), (3, 2, 1)))  # ((1, 2, 3), (4, 5), (6,))
#print(reshape_perm((1, 2, 3, 4), (2, 2)))           # ((1, 2), (3, 4))
#print(reshape_perm((1, 2, 3, 4, 5), (3, 1, 1)))     # ((1, 2, 3), (4,), (5,))

def generate_all_SYTs(shapes):
    """
    Generate all valid SYTs for the given shapes.

    Parameters:
    - shapes (List[Tuple[int]]): A list of shapes to generate SYTs for.

    Returns:
    - Dict[str, List[Tuple[Tuple[int]]]]: A dictionary where keys are shape strings and values are lists of valid SYTs.
    """
    all_SYTs = {}

    for shape in shapes:
        n = sum(shape)
        permutations = itertools.permutations(range(1, n + 1))
        valid_SYTs = []

        for perm in permutations:
            tableau = reshape_perm(perm, shape)
            if is_valid_SYT(tableau):
                valid_SYTs.append(tableau)

        shape_str = "_".join(map(str, shape))
        all_SYTs[shape_str] = valid_SYTs

    return all_SYTs

# Define the shapes
shapes = [(4, 3, 2, 1), (2, 2), (3, 3), (4, 4), (5, 5)]

# Generate all SYTs
all_SYTs = generate_all_SYTs(shapes)

# Example: Save SYTs for each shape to a file (in the data subfolder)
import os

data_dir = "data"
os.makedirs(data_dir, exist_ok=True)

for shape_str, syts in all_SYTs.items():
    with open(os.path.join(data_dir, f"SYTs_{shape_str}.txt"), "w") as file:
        for syt in syts:
            file.write(str(syt) + "\n")


def random_SYT(shape):
    """
    Generates a random Standard Young Tableau (SYT) of the given shape.

    Parameters:
    - shape (Tuple[int]): The shape of the resulting SYT as a tuple of integers.

    Returns:
    - Tuple[Tuple[int]]: A random valid SYT generated based on the given shape.

    This function generates a random permutation of numbers from 1 to n+1, where n is the sum of the elements in the `shape` tuple. It then reshapes the permutation into a tableau using the `reshape_perm` function. If the resulting tableau is not valid, it shuffles the permutation and tries again. The function continues this process until a valid SYT is found, and then returns the reshaped permutation as a tableau.

    Example:
    >>> random_SYT((2, 1))
    ((1, 2), (3,))
    """
    n = sum(shape)
    while True:
        perm = tuple(random.sample(range(1, n+1), n))
        tableau = reshape_perm(perm, shape)
        if is_valid_SYT(tableau):
            return tableau
        
#print(random_SYT((2, 2, 2)))

import random

def random_SYT2(shape):
    """
    Generates a random Standard Young Tableau (SYT) of the given shape.

    Parameters:
    - shape (Tuple[int]): The shape of the resulting SYT as a tuple of integers.

    Returns:
    - Tuple[Tuple[int]]: A random valid SYT generated based on the given shape.
    """
    def generate_random_tableau(shape):
        """
        Generate a tableau by filling numbers from 1 to n in the shape greedily.

        Parameters:
        - shape (Tuple[int]): The shape of the tableau.

        Returns:
        - List[List[int]]: The generated tableau.
        """
        tableau = [[0] * length for length in shape]
        n = sum(shape)
        numbers = list(range(1, n + 1))
        random.shuffle(numbers)

        index = 0
        for i in range(len(shape)):
            for j in range(shape[i]):
                tableau[i][j] = numbers[index]
                index += 1
        
        return [tuple(row) for row in tableau]

    while True:
        tableau = generate_random_tableau(shape)
        if is_valid_SYT(tableau):
            return tuple(tableau)

# Example usage
#print(random_SYT2((2, 1)))  # Example: ((1, 2), (3,))
#print(random_SYT2((3, 2)))  # Example: ((1, 2, 3), (4, 5))
#print(random_SYT2((3, 2, 1)))  # Example: ((1, 2, 3), (4, 5), (6,))

