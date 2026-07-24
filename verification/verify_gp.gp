\\ Independent PARI/GP reconstruction and high-precision numerical check.
\\ Tested by the submitter with PARI/GP 2.17.2.
{
  default(realprecision, 120);

  B = 3084;
  Q = 2*B + 1;
  G = [312,315,336,416,420];
  INF = 10^20;

  reach = vector(10001);
  reach[1] = 1; \\ index n+1 represents n
  for(n = 0, 10000,
    if(reach[n+1],
      for(i = 1, #G,
        if(n + G[i] <= 10000, reach[n + G[i] + 1] = 1)
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
  for(n = 0, 10000-312,
    if(cond < 0 && sum(j = 0, 311, reach[n+j+1]) == 312, cond = n)
  );

  if(#M != 901, error("wrong mask size"));
  if(M[1] != 0 || M[#M] != B, error("wrong mask endpoints"));
  if(sum_size != 3882, error("wrong sum support size"));
  if(diff_size != 6003, error("wrong difference support size"));
  if(diff_cost[B+2] != 1463, error("wrong kappa(1)"));
  if(cond != 4574, error("wrong conductor"));

  lambda = 0.0016039887760343438;
  Pplus = sum(s = 0, 2*B, if(sum_present[s+1], exp(-lambda*s), 0));
  Pminus = sum(i = 1, #diff_cost,
               if(diff_cost[i] < INF, exp(-lambda*diff_cost[i]), 0));
  F = log(Pminus/Pplus);
  th = 1 + F/log(Q); \\ 'theta' is a built-in PARI/GP function name

  print("Exact combinatorial reconstruction: PASS");
  print("B=", B, " base=", Q, " |M|=", #M, " |M+M|=", sum_size,
        " |M-M|=", diff_size, " conductor=", cond,
        " kappa(1)=", diff_cost[B+2]);
  print("Pminus = ", Pminus);
  print("Pplus  = ", Pplus);
  print("F      = ", F);
  print("theta  = ", th);
  if(th <= 1.19023813,
    error("numerical value did not exceed conservative bound")
  );
  print("PASS: high-precision PARI/GP value exceeds 1.19023813");
}
