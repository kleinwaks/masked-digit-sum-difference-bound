\\ Independent PARI/GP reconstruction and high-precision numerical check.
\\ Tested by the submitter with PARI/GP 2.17.2.
{
  default(realprecision, 120);

  B = 17032;
  Q = 2*B + 1;
  G = [1518,1524,1587,2024,2032,2116];
  INF = 10^20;
  LIMIT = 40000;

  reach = vector(LIMIT + 1);
  reach[1] = 1; \\ index n+1 represents n
  for(n = 0, LIMIT,
    if(reach[n+1],
      for(i = 1, #G,
        if(n + G[i] <= LIMIT, reach[n + G[i] + 1] = 1)
      )
    )
  );

  M = List();
  for(n = 0, B, if(reach[n+1], listput(M, n)));
  M = Vec(M);

  sum_present = vector(2*B + 1);
  diff_cost = vector(2*B + 1, i, INF); \\ index d+B+1
  for(i = 1, #M,
    a = M[i];
    for(j = 1, #M,
      b = M[j];
      sum_present[a+b+1] = 1;
      idx = a-b+B+1;
      if(a+b < diff_cost[idx], diff_cost[idx] = a+b)
    )
  );

  sum_size = vecsum(sum_present);
  diff_size = sum(i = 1, #diff_cost, diff_cost[i] < INF);

  cond = -1;
  multiplicity = G[1];
  for(n = 0, LIMIT-multiplicity,
    if(cond < 0 &&
       sum(j = 0, multiplicity-1, reach[n+j+1]) == multiplicity,
       cond = n)
  );

  cover = 0;
  while(cover < B && diff_cost[B+cover+2] < INF, cover = cover + 1);

  if(#M != 3121, error("wrong mask size"));
  if(M[1] != 0 || M[#M] != B, error("wrong mask endpoints"));
  if(sum_size != 18730, error("wrong sum support size"));
  if(diff_size != 32369, error("wrong difference support size"));
  if(cover != 13066, error("wrong initial difference cover"));
  if(diff_cost[B+2] != 14351, error("wrong kappa(1)"));
  if(cond != 28922, error("wrong conductor"));

  lambda = 0.000321149844434550835903084464712287774157626054669874186964;
  Pplus = sum(s = 0, 2*B, if(sum_present[s+1], exp(-lambda*s), 0));
  Pminus = sum(i = 1, #diff_cost,
               if(diff_cost[i] < INF, exp(-lambda*diff_cost[i]), 0));
  F = log(Pminus/Pplus);
  th = 1 + F/log(Q); \\ 'theta' is a built-in PARI/GP function name

  print("Exact combinatorial reconstruction: PASS");
  print("B=", B, " base=", Q, " |M|=", #M, " |M+M|=", sum_size,
        " |M-M|=", diff_size, " cover=", cover, " conductor=", cond,
        " kappa(1)=", diff_cost[B+2]);
  print("Pminus = ", Pminus);
  print("Pplus  = ", Pplus);
  print("F      = ", F);
  print("theta  = ", th);
  if(th <= 1.19102809,
    error("numerical value did not exceed conservative bound")
  );
  print("PASS: high-precision PARI/GP value exceeds 1.19102809");
}
