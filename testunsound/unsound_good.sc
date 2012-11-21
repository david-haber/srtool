void main()
{
	int start;
	assume(start > 0);
	int i;
	i=start;
	while(i)
	bound(2)
	{
		i = i - 1;
	}
	
	// without unwinding assertions, this assert failure should be missed
	
	if(start > 2)
	{
		assert(0);
	}
}

