void main()
{
	int i;
	i=0;
	int j;
	j=0;
	
	while(i < 5)
	bound(5)
	inv(i <= 5)
	{
		j=0;
		while(i > j)
		bound(5)
		inv(j <= i)
		{
			j = j + 1;
		}
		i = i + 1;
	}
	assert(i==j);
}