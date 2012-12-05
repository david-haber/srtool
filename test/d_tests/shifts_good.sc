void main(int i, int j)
{
	i = 5;
	j = i;
	j = j << 2;
	j = j >> 2;
	assert(i == j);
}
