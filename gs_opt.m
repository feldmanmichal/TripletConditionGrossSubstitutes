I = eye(32);
r = @(x) I(sum(bitset(0, char(x) - "a" + 1), 2),:);

h1 = ["da"; "da";
      "db"; "db";
      "ea"; "ea";
      "eb"; "eb"];

h2 = ["eac"; "ebc";
      "eac"; "ebc";
      "dac"; "dbc";
      "dac"; "dbc"];

h = r("ca") + r("deb") - r(h1) - r(h2);

# you can change the order below as you wish. The following two prefixes ensure 
# that you go down the tree to depth 6 only:
# {"acd","b"},{"cae","b"},{"eda","b"},{"ceb","a"},{"ebd","a"},{"ecd","b"}
# {"acd","e"},{"bcd","e"},{"ade","c"},{"ace","d"},{"bce","d"},{"cde","a"}
triples = {...
{"acd","b"},... 
{"cae","b"},...
{"eda","b"},... 
{"ceb","a"},... 
{"ebd","a"},...
{"ecd","b"},...
{"dec","a"},... 
{"dbc","a"},...
{"cde",""}, {"eca",""}, {"deb",""}, {"cdb",""}, {"aed",""}, {"bce",""}, {"dac",""},...
{"aec","d"}, {"bde","c"}, {"bcd","e"}, {"dae","c"}, {"ebc","d"}, {"cda","e"},...
{"cde","ab"}, {"eca","bd"}, {"deb","ac"}, {"cdb","ae"}, {"aed","bc"}, {"bce","ad"}, {"dac","be"},...
{"abc",""}, {"dab",""}, {"bae",""},...
{"bca","d"}, {"abd","c"}, {"aeb","d"},...
{"cab","e"}, {"bda","e"}, {"eba","c"},...
{"abc","de"}, {"dab","ce"}, {"bae","cd"}
};

g1 = [];
g2 = [];

A = [I(32,:); h];
b = [0; ones(8, 1)];
c = zeros(32, 1);
lb = zeros(32, 1);
ub = repmat(Inf, 32, 1);
ctype = ["S"; repmat("L", 8, 1)];
vartype = repmat("C", 32, 1);

for k = triples
  t = k{1}{1};
  s = k{1}{2};
  for j = 1:3
    m = t(j);
    M = erase(t, m);
    g1(end+1,:) = r([M(1) s]) + r([m M(2) s]) - r([M(2) s]) - r([m M(1) s]);
    g2(end+1,:) = r([m s]) + r([M s]) - r([M(1) s]) - r([m M(2) s]);
  endfor
endfor

d = 1;
p = zeros(1,40);
count = 0;
count_ = 0;
maxd = 0;

while (d > 0)
  count++;
  count_++;
  if (count >= 100)
    printf("%d", p);
    printf("\n");
    count_
    count = 0;
  endif
  if (p(d) == 0)
    A(end+1,:) = g1(3*d-2,:);
    A(end+1,:) = g2(3*d-2,:);
    b(end+1,:) = 0;
    b(end+1,:) = 0;
    ctype(end+1,:) = "S";
    ctype(end+1,:) = "U";
  elseif (p(d) == 3)
    p(d) = 0;
    A(end,:) = [];
    A(end,:) = [];
    b(end,:) = [];
    b(end,:) = [];
    ctype(end,:) = [];
    ctype(end,:) = [];
    if (d == 1)
      disp("No counterexample.");
      break
    endif
    d--;
    continue
  else
    A(end-1,:) = g1(3*d-2+p(d),:);
    A(end,:) = g2(3*d-2+p(d),:);
  endif
  
  [xmin, fmin, status, extra] = glpk(c, A, b, lb, ub, ctype, vartype, 1, struct("msglev", 0));
  
  if (status == 10)
    p(d)++;
  elseif (status == 0)
    maxd = max(maxd, d);
    p(d)++;
    if (d == 1)
      disp("Counterexample found.");
      break
    endif
    d++;
  else
    break
  endif
endwhile

