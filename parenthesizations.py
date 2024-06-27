import itertools

def valid(n):
  """
  Returns a list of all possible parenthesizations of length n.

  Parameters:
    n (int): The length of the parenthesizations.

  Returns:
    A list of strings, where each inner string represents a valid parenthesization of length n.
  
  Example:
  >>> parenthesizations(3)
  {'((()))', '(()())', '(())()', '()(())', '()()()'}
  """
  if n == 0:
    return [""]
  else:
    result = []
    for i in range(n):
      for c in valid(i):
        for d in valid(n - i - 1):
          result.append("(" + c + ")" + d)
    return result

def invalid(n):
  """
  Generates a set of all invalid parenthesizations of length 2n.

  Parameters:
    n (int): The length of the parenthesizations.

  Returns:
    set: A set of strings, where each string represents an invalid parenthesization of length 2n.
  
  Example:
  >>> invalid(3)
  {"())())", ")))(((", ...}
  """
  return set("".join(p) for p in itertools.product("()",repeat=2*n)) - set(valid(n))

