test2_1(a).
test2_1(b).
test2_1(c).

test2_2(X, X) :- test2_1(_).
% %FALSE% test2_2(x,y)
% %QUERY% test2_2(X,X)
% %ANSWER% X=UNINSTANTIATED VARIABLE
% %ANSWER% X=UNINSTANTIATED VARIABLE
% %ANSWER% X=UNINSTANTIATED VARIABLE

% %QUERY% test2_2(x,x)
% %ANSWER/%
% %ANSWER/%
% %ANSWER/%

% %QUERY% test2_2(x,X)
% %ANSWER% X=x
% %ANSWER% X=x
% %ANSWER% X=x

% %QUERY% test2_2(X,y)
% %ANSWER% X=y
% %ANSWER% X=y
% %ANSWER% X=y
