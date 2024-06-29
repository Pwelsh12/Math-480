# Summary of findings.

## Statistic 1
**Accuracy achieved:** 
100%

**Description of model weights:**
The heat map of row 1 shows dark blue for the value 1 at each position 1 - (n-1) and is dark red 
when the value 1 is in the nth position.

**How to compute statistic:**
If the value 1 is in the nth position the statistic = 1
else statistic = 0

## Statistic 2
**Accuracy achieved:** 
100%

**Description of model weights:**
From the model weights in row 1 we can see that only the nth and n-1 position
are valuable in determining the statistic. In the n-1 position the color of the 1 value
is deep blue and turns deeper red as the numbers increase.
In the nth position, the color scale is the opposite where the 1 value is a deep red ending 
with the nth value which is a deep blue.  

**How to compute statistic:**
From the model weights we can determine the statistic is found 
by the following rule: 
If the the value in the n-1 position is greater than the nth position 
then the value of the statistic is 1 otherwise the value is 0. 

## Statistic 3
**Accuracy achieved:**
100%

**Description of model weights:**
The model weights in row 1 are either alternating between blue, white and red,
or are in groups of two of the same color. for each value of n, there are strong blues
and reds for specific values in various positions, but they are not a strict rule that
determine the value of the statistic if the permutation contains the value in that position.   

**How to compute statistic:**
Couldnt figure this one out.

## Statistic 4
**Accuracy achieved:**
100%

**Description of model weights:**
In row 1 the model weight shows a deep blue for the value that is equal to the corresponding position in the permutation.
For example, the value 1 has a deep blue in the 1st position of the permutation.

**How to compute statistic:**
The statistic has the value 1 when each of the values in the permutation is in a different position than the starting (1 2 3 4 ... n) permutation
if we denote the values as a_i then the value of the statistic is 1 when each a_i is not in the corresponding ith position of the permutation.

## Statistic 5
**Accuracy achieved:**
99.47916666666667%

**Description of model weights:**
I could not immediately see a clear pattern to the heat map, but in row 1 in the 4th position the values 1 and 2 are represented by
deep blue and the rest of the values are represented by a light red. This is also similar for position 5 but with the values 2 and 3. 

**How to compute statistic:**
I could not figure out the pattern.

## Statistic 6
**Accuracy achieved:**
65.27777777777777%

**Description of model weights:**
Since the accuracy was low I cannot determine if the heatmap is telling me valuable information about the 
pattern to compute the statistic, but from my data in position 1 the values 1 and 2 are deep red and in position 4 the value of 1 is a deep blue.
**How to compute statistic:**
I could not figure out this statistic.

## Statistic 7
**Accuracy achieved:**
99.82638888888889%
**Description of model weights:**
In row 1 there are not any deep colors in the heatmap, but in row 0 and 2 the 4th and 5th positions have deep colors.
In row 0 position 4 the values 6 and 7 are deep blue and in position 5 1 and 7 are deep red.
In row 2 position 4, 3 and 4 are deep blue and then 1 and 2 are deep red and in position 5 the values 2 and 3 are deep blue.
**How to compute statistic:**
I could not figure out the pattern.

## Statistic 8
**Accuracy achieved:**
99.65277777777777%
**Description of model weights:**
In row 1, position 2 there the value 1 is a deep blue, in position 4 the value 4 is a deep blue and in position 5 the value 5 is deep blue.
There are no deep red values.
**How to compute statistic:**
I could not get the pattern.
## Statistic 9
**Accuracy achieved:**
99.47916666666667%
**Description of model weights:**
For each row, there are not any deep colors on the heatmap.
In row 1 in position 6 the values are evenly red and blue with deeper colors towards the middle and 
getting lighter towards the ends. 
**How to compute statistic:**
I could not figure out the pattern.