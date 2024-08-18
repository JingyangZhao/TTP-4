#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <map>
#include <sstream>
#include <algorithm>
#include <cmath>
#include <random>
#include <cstdlib>
#include <ctime>
#include <iomanip>

#include <direct.h>
#include <stdio.h>

using namespace std;

#define total_number_left 1

#define total_number_last 1

#define INT_MAX 1e9

// The following code is for the minimum weight matching algorithm
typedef long long s64;

const int INF = 2147483647;

const int MaxN = 400;
const int MaxM = 79800;

template <class T>
inline void tension(T &a, const T &b)
{
	if (b < a)
		a = b;
}
template <class T>
inline void relax(T &a, const T &b)
{
	if (b > a)
		a = b;
}
template <class T>
inline int size(const T &a)
{
	return (int)a.size();
}

inline int getint()
{
	char c;
	while (c = getchar(), '0' > c || c > '9');

	int res = c - '0';
	while (c = getchar(), '0' <= c && c <= '9')
		res = res * 10 + c - '0';
	return res;
}

const int MaxNX = MaxN + MaxN;

struct edge
{
	int v, u, w;

	edge(){}
	edge(const int &_v, const int &_u, const int &_w)
		: v(_v), u(_u), w(_w){}
};

int N, M;
edge mat[MaxNX + 1][MaxNX + 1];

int n_matches;
s64 tot_weight;
int mate[MaxNX + 1];
int lab[MaxNX + 1];

int q_n, q[MaxN];
int fa[MaxNX + 1], col[MaxNX + 1];
int slackv[MaxNX + 1];

int n_x;
int bel[MaxNX + 1], blofrom[MaxNX + 1][MaxN + 1];
vector<int> bloch[MaxNX + 1];

inline int e_delta(const edge &e) // does not work inside blossoms
{
	return lab[e.v] + lab[e.u] - mat[e.v][e.u].w * 2;
}
inline void update_slackv(int v, int x)
{
	if (!slackv[x] || e_delta(mat[v][x]) < e_delta(mat[slackv[x]][x])) slackv[x] = v;
}
inline void calc_slackv(int x)
{
	slackv[x] = 0;
	for (int v = 1; v <= N; v++) if (mat[v][x].w > 0 && bel[v] != x && col[bel[v]] == 0) update_slackv(v, x);
}
inline void q_push(int x)
{
	if (x <= N)
		q[q_n++] = x;
	else
	{
		for (int i = 0; i < size(bloch[x]); i++) q_push(bloch[x][i]);
	}
}
inline void set_mate(int xv, int xu)
{
	mate[xv] = mat[xv][xu].u;
	if (xv > N)
	{
		edge e = mat[xv][xu];
		int xr = blofrom[xv][e.v];
		int pr = find(bloch[xv].begin(), bloch[xv].end(), xr) - bloch[xv].begin();
		if (pr % 2 == 1)
		{
			reverse(bloch[xv].begin() + 1, bloch[xv].end());
			pr = size(bloch[xv]) - pr;
		}

		for (int i = 0; i < pr; i++) set_mate(bloch[xv][i], bloch[xv][i ^ 1]);
		set_mate(xr, xu);

		rotate(bloch[xv].begin(), bloch[xv].begin() + pr, bloch[xv].end());
	}
}
inline void set_bel(int x, int b)
{
	bel[x] = b;
	if (x > N)
	{
		for (int i = 0; i < size(bloch[x]); i++) set_bel(bloch[x][i], b);
	}
}
inline void augment(int xv, int xu)
{
	while (true)
	{
		int xnu = bel[mate[xv]];
		set_mate(xv, xu);
		if (!xnu) return;
		set_mate(xnu, bel[fa[xnu]]);
		xv = bel[fa[xnu]], xu = xnu;
	}
}
inline int get_lca(int xv, int xu)
{
	static bool book[MaxNX + 1];
	for (int x = 1; x <= n_x; x++) book[x] = false;
	while (xv || xu)
	{
		if (xv)
		{
			if (book[xv]) return xv;
			book[xv] = true;
			xv = bel[mate[xv]];
			if (xv) xv = bel[fa[xv]];
		}
		swap(xv, xu);
	}
	return 0;
}
inline void add_blossom(int xv, int xa, int xu)
{
	int b = N + 1;
	while (b <= n_x && bel[b]) b++;
	if (b > n_x) n_x++;

	lab[b] = 0;
	col[b] = 0;

	mate[b] = mate[xa];

	bloch[b].clear();
	bloch[b].push_back(xa);
	for (int x = xv; x != xa; x = bel[fa[bel[mate[x]]]]) bloch[b].push_back(x), bloch[b].push_back(bel[mate[x]]), q_push(bel[mate[x]]);

	reverse(bloch[b].begin() + 1, bloch[b].end());

	for (int x = xu; x != xa; x = bel[fa[bel[mate[x]]]]) bloch[b].push_back(x), bloch[b].push_back(bel[mate[x]]), q_push(bel[mate[x]]);

	set_bel(b, b);

	for (int x = 1; x <= n_x; x++)
	{
		mat[b][x].w = mat[x][b].w = 0;
		blofrom[b][x] = 0;
	}
	for (int i = 0; i < size(bloch[b]); i++)
	{
		int xs = bloch[b][i];
		for (int x = 1; x <= n_x; x++) if (mat[b][x].w == 0 || e_delta(mat[xs][x]) < e_delta(mat[b][x])) mat[b][x] = mat[xs][x], mat[x][b] = mat[x][xs];
		for (int x = 1; x <= n_x; x++) if (blofrom[xs][x]) blofrom[b][x] = xs;
	}
	calc_slackv(b);
}
inline void expand_blossom1(int b) // lab[b] == 1
{
	for (int i = 0; i < size(bloch[b]); i++)
		set_bel(bloch[b][i], bloch[b][i]);

	int xr = blofrom[b][mat[b][fa[b]].v];
	int pr = find(bloch[b].begin(), bloch[b].end(), xr) - bloch[b].begin();
	if (pr % 2 == 1)
	{
		reverse(bloch[b].begin() + 1, bloch[b].end());
		pr = size(bloch[b]) - pr;
	}

	for (int i = 0; i < pr; i += 2)
	{
		int xs = bloch[b][i], xns = bloch[b][i + 1];
		fa[xs] = mat[xns][xs].v;
		col[xs] = 1, col[xns] = 0;
		slackv[xs] = 0, calc_slackv(xns);
		q_push(xns);
	}
	col[xr] = 1;
	fa[xr] = fa[b];
	for (int i = pr + 1; i < size(bloch[b]); i++)
	{
		int xs = bloch[b][i];
		col[xs] = -1;
		calc_slackv(xs);
	}

	bel[b] = 0;
}
inline void expand_blossom_final(int b)
{
	for (int i = 0; i < size(bloch[b]); i++)
	{
		if (bloch[b][i] > N && lab[bloch[b][i]] == 0) expand_blossom_final(bloch[b][i]);
		else set_bel(bloch[b][i], bloch[b][i]);
	}

	bel[b] = 0;
}

inline bool on_found_edge(const edge &e)
{
	int xv = bel[e.v], xu = bel[e.u];
	if (col[xu] == -1)
	{
		int nv = bel[mate[xu]];
		fa[xu] = e.v;
		col[xu] = 1, col[nv] = 0;
		slackv[xu] = slackv[nv] = 0;
		q_push(nv);
	}
	else if (col[xu] == 0)
	{
		int xa = get_lca(xv, xu);
		if (!xa)
		{
			augment(xv, xu), augment(xu, xv);
			for (int b = N + 1; b <= n_x; b++)
				if (bel[b] == b && lab[b] == 0)
					expand_blossom_final(b);
			return true;
		}
		else add_blossom(xv, xa, xu);
	}

	return false;
}

bool match()
{
	for (int x = 1; x <= n_x; x++) col[x] = -1, slackv[x] = 0;

	q_n = 0;
	for (int x = 1; x <= n_x; x++) if (bel[x] == x && !mate[x]) fa[x] = 0, col[x] = 0, slackv[x] = 0, q_push(x);

	if (q_n == 0) return false;

	while (true)
	{
		for (int i = 0; i < q_n; i++)
		{
			int v = q[i];
			for (int u = 1; u <= N; u++)
				if (mat[v][u].w > 0 && bel[v] != bel[u])
				{
					int d = e_delta(mat[v][u]);
					if (d == 0)
					{
						if (on_found_edge(mat[v][u])) return true;
					}
					else if (col[bel[u]] == -1 || col[bel[u]] == 0) update_slackv(v, bel[u]);
				}
		}

		int d = INF;
		for (int v = 1; v <= N; v++) if (col[bel[v]] == 0) tension(d, lab[v]);

		for (int b = N + 1; b <= n_x; b++) if (bel[b] == b && col[b] == 1) tension(d, lab[b] / 2);

		for (int x = 1; x <= n_x; x++)
		{
			if (bel[x] == x && slackv[x])
			{
				if (col[x] == -1)
					tension(d, e_delta(mat[slackv[x]][x]));
				else if (col[x] == 0)
					tension(d, e_delta(mat[slackv[x]][x]) / 2);
			}
		}

		for (int v = 1; v <= N; v++)
		{
			if (col[bel[v]] == 0) lab[v] -= d;
			else if (col[bel[v]] == 1) lab[v] += d;
		}

		for (int b = N + 1; b <= n_x; b++)
			if (bel[b] == b)
			{
				if (col[bel[b]] == 0) lab[b] += d * 2;
				else if (col[bel[b]] == 1) lab[b] -= d * 2;
			}

		q_n = 0;
		for (int v = 1; v <= N; v++) if (lab[v] == 0) return false;

		for (int x = 1; x <= n_x; x++)
			if (bel[x] == x && slackv[x] && bel[slackv[x]] != x && e_delta(mat[slackv[x]][x]) == 0)
			{
				if (on_found_edge(mat[slackv[x]][x]))
					return true;
			}

		for (int b = N + 1; b <= n_x; b++) if (bel[b] == b && col[b] == 1 && lab[b] == 0) expand_blossom1(b);
	}
	return false;
}

void maxmatching()
{
	n_x = N, n_matches = 0, tot_weight = 0;
	for (int v = 1; v <= N; v++) mate[v] = 0;

	bel[0] = 0;
	for (int v = 1; v <= N; v++) bel[v] = v, bloch[v].clear();
	for (int v = 1; v <= N; v++) for (int u = 1; u <= N; u++) blofrom[v][u] = v == u ? v : 0;

	int w_max = 0;
	for (int v = 1; v <= N; v++) for (int u = 1; u <= N; u++) relax(w_max, mat[v][u].w);
	for (int v = 1; v <= N; v++) lab[v] = w_max;

	while (match()) n_matches++;

	for (int v = 1; v <= N; v++) if (mate[v] && mate[v] < v) tot_weight += mat[v][mate[v]].w;
}

int minmatching(int n, vector<vector<int> > &Matrix)
{
	N = n, M = N*(N-1)/2;
	for (int v = 1; v <= N; v++)
		for (int u = 1; u <= N; u++)
			mat[v][u] = edge(v, u, 0);
	
	for(int i=1; i<=N; i++)
		for(int j=i+1; j<=N; j++)
		{
			int w = Matrix[i][j];
			w = -w+1000000;
			mat[i][j].w = mat[j][i].w = w;
		}
	maxmatching();
	
	// the value of the minimum weight minmatching
	return N/2*1000000-tot_weight;
}
// End of the minimum weight matching algorithm

// Store the design of the left super-game and last super-game
int left_super_game[total_number_left+1][8+1][8+1];
int last_super_game[total_number_last+1][8+1][14+1];

void fight(int a1,int b1, int a2,int b2, int a3,int b3, int a4,int b4, int f, int d, vector<vector<int> > &day)
{
	day[a1][d]=f*b1, day[b1][d]=-f*a1;
	day[a2][d]=f*b2, day[b2][d]=-f*a2;
	day[a3][d]=f*b3, day[b3][d]=-f*a3;
	day[a4][d]=f*b4, day[b4][d]=-f*a4;
}
void lable(int i, vector<int> a, vector<int> &aa)
{
	int n1=(i-1)/6+1; i=i%6; if(i==0) i=6; int n2=(i-1)/2+1; if(n2>=n1) n2++; i=i%2; if(i==0) i=2; int n3=(i-1)+1; if(n3>=min(n1,n2)) n3++; if(n3>=max(n1,n2)) n3++; int n4=1+2+3+4-n1-n2-n3;
	aa[1]=a[n1], aa[2]=a[n2], aa[3]=a[n3], aa[4]=a[n4];
}
void type_normal(vector<int> &a, vector<int> &b, int s, int f, vector<vector<int> > &day, int d)
{
	if(s==1) fight(a[1],b[1], a[2],b[2], a[3],b[3], a[4],b[4], f, d, day);
	else if(s==2) fight(a[1],b[2], a[2],b[1], a[3],b[4], a[4],b[3], f, d, day);
	else if(s==3) fight(a[1],b[3], a[2],b[4], a[3],b[1], a[4],b[2], f, d, day);
	else fight(a[1],b[4], a[2],b[3], a[3],b[2], a[4],b[1], f, d, day);
}
int ex_normal(vector<int> &a, vector<int> &b, vector<vector<int> > &Matrix)
{
	int cost = 2*( Matrix[a[1]][b[1]]+Matrix[a[2]][b[2]]+Matrix[a[3]][b[3]]+Matrix[a[4]][b[4]] );
	cost += 2*( Matrix[a[1]][b[4]]+Matrix[a[2]][b[3]]+Matrix[a[3]][b[2]]+Matrix[a[4]][b[1]] );
	cost += 4*Matrix[a[1]][a[2]]+4*Matrix[a[3]][a[4]]+2*Matrix[a[2]][a[3]]+2*Matrix[a[1]][a[4]];
	cost += 4*Matrix[b[1]][b[2]]+4*Matrix[b[3]][b[4]]+2*Matrix[b[2]][b[3]]+2*Matrix[b[1]][b[4]];
	return cost;
}
void type_normal(vector<int> &a, vector<int> &b, int f, vector<vector<int> > &day, int d, vector<vector<int> > &Matrix)
{
	if(f == -1) type_normal(b, a, -f, day, d, Matrix);
	else
	{
		vector<int> aa(5), bb(5);
		int min1=ex_normal(a, b, Matrix), x1=1, y1=1;
		for(int i=1; i<=24; i++)
		{
			for(int j=1; j<=24; j++)
			{
				lable(i, a, aa), lable(j, b, bb);
				int temp = ex_normal(aa, bb, Matrix);
				if(temp<min1) min1=temp, x1=i, y1=j;
			}
		}
		// find the best labels of teams in S_a and S_b
		lable(x1, a, aa); lable(y1, b, bb);
		type_normal(aa,bb,1,1,day,d+0); type_normal(aa,bb,2,1,day,d+1); type_normal(aa,bb,3,1,day,d+2); type_normal(aa,bb,4,1,day,d+3);
		type_normal(aa,bb,1,-1,day,d+4); type_normal(aa,bb,2,-1,day,d+5); type_normal(aa,bb,3,-1,day,d+6); type_normal(aa,bb,4,-1,day,d+7);
	}
}
int ex_left_super_game(int t, vector<int> &aa, vector<int> &bb, vector<vector<int> > &Matrix)
{
 	int res=0, o[9]={0, aa[1],aa[2],aa[3],aa[4], bb[1],bb[2],bb[3],bb[4]};
	for(int i=1; i<=8; i++)
	{
		int flag=0;
		for(int d=1; d<=8; d++)
			if(d==8 && left_super_game[t][i][d]>0)
				if(flag==0) res += 2*Matrix[ o[i] ][ o[left_super_game[t][i][d]] ];	
				else res += Matrix[ o[left_super_game[t][i][d-1]] ][ o[left_super_game[t][i][d]] ]+Matrix[ o[left_super_game[t][i][d]] ][ o[i] ];
			else if(left_super_game[t][i][d]<0)
				if(flag==0) continue; 
				else res += Matrix[ o[i] ][ o[left_super_game[t][i][d-1]] ], flag=0;
			else
				if(flag==0) res += Matrix[ o[i] ][ o[left_super_game[t][i][d]] ], flag=1;
				else res += Matrix[ o[left_super_game[t][i][d-1]] ][ o[left_super_game[t][i][d]] ];		
	} 
	return res;
}
void type_L(vector<int> &a, vector<int> &b, int f, vector<vector<int> > &day, int d, vector<vector<int> > &Matrix)
{ 
	if(f==-1) type_L(b, a, -f, day, d, Matrix);
	else{
		vector<int> aa(5), bb(5); 
		int min=INT_MAX, t1,x1,y1;
		for(int t=1; t<=total_number_left; t++)
		{
			for(int i=1; i<=24; i++)
			{
				for(int j=1; j<=24; j++)
				{	
					lable(i, a, aa); lable(j, b, bb);
					int temp = ex_left_super_game(t, aa, bb, Matrix);
					if(temp<min) min=temp, t1=t, x1=i, y1=j;
				}
			}
		}
		// find the best labels of teams in S_a and S_b
		lable(x1, a, a), lable(y1, b, b);
		int o[9]={0, a[1],a[2],a[3],a[4], b[1],b[2],b[3],b[4]};
		 
		for(int i=1; i<=8; i++) 
			for(int j=1; j<=8; j++) 
				if(left_super_game[t1][i][j]>0) day[ o[i] ][d+j-1] = o[left_super_game[t1][i][j]];
				else day[ o[i] ][d+j-1] = -o[-left_super_game[t1][i][j]];
				
		vector<int>().swap(aa), vector<int>().swap(bb);
	}
}
int ex_last_super_game(int t, vector<int> &aa, vector<int> &bb, vector<vector<int> > &Matrix)
{
 	int res=0, o[9]={0, aa[1],aa[2],aa[3],aa[4], bb[1],bb[2],bb[3],bb[4]};
	
	for(int i=1; i<=8; i++)
	{
		int flag=0;
		for(int d=1; d<=14; d++)
			if(d==14 && last_super_game[t][i][d]>0)
				if(flag==0) res += 2*Matrix[ o[i] ][ o[last_super_game[t][i][d]] ];	
				else res += Matrix[ o[last_super_game[t][i][d-1]] ][ o[last_super_game[t][i][d]] ]+Matrix[ o[last_super_game[t][i][d]] ][ o[i] ];
			else if(last_super_game[t][i][d]<0)
				if(flag==0) continue; 
				else res += Matrix[ o[i] ][ o[last_super_game[t][i][d-1]] ], flag=0;
			else
				if(flag==0) res += Matrix[ o[i] ][ o[last_super_game[t][i][d]] ], flag=1;
				else res += Matrix[ o[last_super_game[t][i][d-1]] ][ o[last_super_game[t][i][d]] ];		
	} 
	return res;
}
void type_last(vector<int> &a, vector<int> &b, int f, vector<vector<int> > &day, int d, vector<vector<int> > &Matrix)
{ 
	if(f==-1) type_last(b, a, -f, day, d, Matrix);
	else{
		vector<int> aa(5), bb(5); 
		int min=INT_MAX, t1,x1,y1;
		for(int t=1; t<=total_number_last; t++)
		{
			for(int i=1; i<=24; i++)
			{
				for(int j=1; j<=24; j++)
				{			
					lable(i, a, aa); lable(j, b, bb);
					int temp = ex_last_super_game(t, aa, bb, Matrix);
					if(temp<min) min=temp, t1=t, x1=i, y1=j;
				}
			}
		}
		// find the best labels of teams in S_a and S_b
		lable(x1, a, a), lable(y1, b, b);
		int o[9]={0, a[1],a[2],a[3],a[4], b[1],b[2],b[3],b[4]};
		 
		for(int i=1; i<=8; i++) 
			for(int j=1; j<=14; j++) 
				if(last_super_game[t1][i][j]>0) day[ o[i] ][d+j-1] = o[last_super_game[t1][i][j]];
				else day[ o[i] ][d+j-1] = -o[-last_super_game[t1][i][j]];
				
		vector<int>().swap(aa), vector<int>().swap(bb);
	}
}
//check for the feasibility
int check(int n, vector<vector<int> > &day)
{
	int num = n;
	// check the at-most-4 constraint
	for(int i=1; i<=n; i++)
	{
		for(int d=1; d<=n*2-4-2; d++)
		{
			if(day[i][d]>0 && day[i][d+1]>0 && day[i][d+2]>0 && day[i][d+3]>0 && day[i][d+4]>0) return -1;
			if(day[i][d]<0 && day[i][d+1]<0 && day[i][d+2]<0 && day[i][d+3]<0 && day[i][d+4]<0) return -1;
		}
	}
	// check if it is a double round-robin tournament
	for(int i=1; i<=n; i++)
	{
		for(int d=1; d<=n*2-2; d++)
		{
			int ooop = abs(day[i][d]);
			if(abs(day[ooop][d]) != i) return -1;
		}
	}
	vector<vector<int> > fd(n+1, vector<int>(n+1));
	for(int i=1; i<=n; i++) for(int k=1; k<=2*n-2; k++) if(day[i][k]>0) fd[i][day[i][k]]+=1;
	for(int i=1; i<=n; i++) for(int j=1; j<=n; j++) if(i!=j && fd[i][j]!=1) return -1;
	for(int i=1; i<=n; i++) for(int d=1; d<=n*2-1-2; d++) if(abs(day[i][d]) == abs(day[i][d+1])) return -1;
	
	return 0;
} 
void show_table(vector<vector<int> > &day, int n)
{
	printf("/**************table****************/\n"); 
	for(int i=1; i<=n; i++,printf("\n"))
		for(int j=1; j<=2*n-2; j++)
			printf("%3d",day[i][j]);
}
//calculate the total distance travelled by all teams from the 1-st day to the ed-th day
int travelingdistance(int n, int ed, vector<vector<int> > &day,  vector<vector<int> > &Matrix)
{
	int res=0;
	for(int i=1; i<=n; i++)
	{
		int flag=0;
		for(int d=1; d<=ed; d++)
			if(d==ed && day[i][d]>0)
				if(flag==0) res += 2*Matrix[i][day[i][d]];	
				else res += Matrix[day[i][d-1]][day[i][d]]+Matrix[day[i][d]][i];
			else if(day[i][d]<0)
				if(flag==0) continue; 
				else res += Matrix[i][day[i][d-1]], flag=0;
			else
				if(flag==0) res += Matrix[i][day[i][d]], flag=1;
				else res += Matrix[day[i][d-1]][day[i][d]];		
	} 
	return res;
}

int ttp(vector<vector<int> > &Matrix, vector<vector<int> > &day, vector<vector<int> > &S)
{
	int n = Matrix.size() - 1;

	int m = n/4, f = 1;
	
	for(int i=1; i<=m-1; i++)
	{
		//S_0 = S_{m-2}
		int o = 1-i; if(o<=0) o = m-1+o;
		
		int ff = f, aa, bb;
		for(int j=1; j<=(m-2)/2; j++)
		{
			aa = o+j, bb = o-j; aa += 2*(m-1), bb +=  2*(m-1); aa = aa%(m-1), bb = bb%(m-1);
			if(aa==0) aa=(m-1); if(bb==0) bb=(m-1);
			if(i != m-1) type_normal(S[aa], S[bb], ff, day, 8*i-7, Matrix);
			else type_last(S[aa], S[bb], ff, day, 8*i-7, Matrix);
			
			ff = -ff;
		}

		if(i==1 && m>2) type_normal(S[o], S[m], -f, day, 8*i-7, Matrix);
		else if(i != m-1) type_L(S[o], S[m], f, day, 8*i-7, Matrix);
		else type_last(S[o], S[m], f, day, 8*i-7, Matrix);

		f=-f;
	}

	if(check(n, day)==-1) {printf("error");}
	
	//show_table(day,n);
	//calculate the distance
	int res = travelingdistance(n, 2*n-2, day, Matrix);
	
	return res;
}

void random_order(int n, vector<vector<int> > &S)
{
	//random order super-teams and swap pair of teams in each super-team
	int m=n/4;
	vector<vector<int> > u_(n/4+1, vector<int>(5));
	
	vector<int> list_number; 
	
	for(int i=1; i<=m; i++) list_number.push_back(i);
	
	random_shuffle(list_number.begin(), list_number.end());
	
	for(int i=1; i<=m; i++) for(int j=1; j<=4; j++) u_[i][j]=S[list_number[i-1]][j]; //swap_ui(i, u_);
	
	for(int i=1; i<=m; i++) for(int j=1; j<=4; j++) S[i][j]=u_[i][j];
	
	vector<int>().swap(list_number);
}

void swap_Sij(int i, int j, vector<vector<int> > &S)
{
	int t; for(int k=1; k<=4; k++) t=S[i][k], S[i][k]=S[j][k], S[j][k]=t;
}

int swap_super_team(int n, int &solution, vector<vector<int> > &S, vector<vector<int> > &day, vector<vector<int> > &Matrix)
{
	int m=n/4, opt_flag=0;
	vector<pair<int, int> > list_m;
	for(int i=1; i<=m; i++) for(int j=i+1; j<=m; j++) list_m.push_back(make_pair(i,j));
	int flag=1;
	while(flag){
		random_shuffle(list_m.begin(), list_m.end());
		for(int i=0; i<list_m.size(); i++) {
			swap_Sij(list_m[i].first, list_m[i].second, S);
			int newsolution = ttp(Matrix, day, S);
			if(newsolution<solution) solution = newsolution, flag=2, opt_flag=1; 
			else swap_Sij(list_m[i].first, list_m[i].second, S);
		} flag--;
	}
	vector<pair<int, int> >().swap(list_m);
	return opt_flag;
}

void read_Matrix(const string& filename, vector<vector<int> > &Matrix, int &n)
{
	ifstream infile(filename);
    for(int i=1; i<=n; i++)
        for(int j=1; j<=n; j++){
            int x; infile >> x; Matrix[i][j] = x;
        }
    infile.close();
}
/*********************************************************************************/
void ouralgorithm(string &file, int &n, int &solution)
{
	vector<vector<int> > Matrix(n+1,vector<int>(n+1));

	// read the distance matrix
	read_Matrix(file, Matrix, n);

	vector<vector<int> > day(n+1, vector<int>(2*n-2+1));
	
	//the first minimum weight matching
	minmatching(n, Matrix);

	pair<int, int> M[n/2+1];
	for (int v = 1, f=1; v <= n; v++) if(mate[v]!=-1) M[f]=make_pair(v,mate[v]), mate[mate[v]]=-1, f++;
	
	//the second mimimum weight matching to pair super-teams
	vector<vector<int> > HM(n/2+1,vector<int>(n/2+1));
	for(int i=1; i<=n/2; i++)
	{
		HM[i][i] = 0;
		for(int j=i+1; j<=n/2; j++)
		{
			int t1=Matrix[M[i].first][M[j].first]+Matrix[M[i].second][M[j].second], 
					t2=Matrix[M[i].first][M[j].second]+Matrix[M[i].second][M[j].first];
					
			HM[i][j] = t1<t2? t1:t2; HM[j][i] = HM[i][j]; //1234  2143  3412 4321
		}
	}
	minmatching(n/2, HM);
	
	//label super-teams, where each super-team contains 4 teams
	vector<vector<int> > S(n/4+1, vector<int>(5));
	for (int v = 1, f=1; v <= n/2; v++) 
		if(mate[v]!=-1) {S[f][1]=M[v].first, S[f][2]=M[v].second, S[f][3]=M[mate[v]].first, S[f][4]=M[mate[v]].second; mate[mate[v]]=-1, f++;}	
	
	//random order super-teams
	random_order(n, S);
	
    //calculate the initial schedule
	solution = ttp(Matrix, day, S);
	
	// pair-wise swapping heuristic
	while(swap_super_team(n, solution, S, day, Matrix)){}

	for (auto& vec : Matrix) vector<int>().swap(vec); vector<vector<int>>().swap(Matrix);
	for (auto& vec : day) vector<int>().swap(vec); vector<vector<int>>().swap(day);
	for (auto& vec : HM) vector<int>().swap(vec); vector<vector<int>>().swap(HM);
}

void read_table_left_super_game(FILE *fp, int table_num, int n_6_table[][9][9])
{
	if(!fp)exit(0);
	for(int t=1; t<=table_num; t++) for(int i=1; i<=8; i++) for(int j=1; j<=8; j++) fscanf(fp, "%d",&left_super_game[t][i][j]);
	fclose(fp);
}
void read_table_last_super_game(FILE *fp, int table_num, int n_6_table[][9][15])
{
	if(!fp)exit(0); int n=8;
	for(int t=1; t<=table_num; t++) for(int i=1; i<=n; i++) for(int j=1; j<=2*n-2; j++) fscanf(fp, "%d",&last_super_game[t][i][j]);
	fclose(fp);
}

// Instances with n mod 8 = 0
vector<string> filesA = {
"TTP//Instance//Galaxy40.txt",
"TTP//Instance//Galaxy32.txt",
"TTP//Instance//Galaxy24.txt",
"TTP//Instance//Galaxy16.txt",
"TTP//Instance//NFL32.txt",
"TTP//Instance//NFL24.txt",
"TTP//Instance//NFL16.txt",
"TTP//Instance//NL16.txt",
"TTP//Instance//Brazil24.txt"
};
// Instances with n mod 8 = 2
vector<string> filesB = {
"TTP//Instance//Galaxy34.txt",
"TTP//Instance//Galaxy26.txt",
"TTP//Instance//Galaxy18.txt",
"TTP//Instance//NFL26.txt",
"TTP//Instance//NFL18.txt"
};
// Instances with n mod 8 = 4
vector<string> filesC = {
"TTP//Instance//Galaxy36.txt",
"TTP//Instance//Galaxy28.txt",
"TTP//Instance//Galaxy20.txt",
"TTP//Instance//NFL28.txt",
"TTP//Instance//NFL20.txt"
};
// Instances with n mod 8 = 6
vector<string> filesD = {
"TTP//Instance//Galaxy38.txt",
"TTP//Instance//Galaxy30.txt",
"TTP//Instance//Galaxy22.txt",
"TTP//Instance//NFL30.txt",
"TTP//Instance//NFL22.txt"
};

int main()
{
	vector<string> filesAll;
    //9 + 5 + 5 + 5
    for(auto & file: filesA) filesAll.push_back(file); // Instances with n mod 8 = 0
    for(auto & file: filesB) filesAll.push_back(file); // Instances with n mod 8 = 2
    for(auto & file: filesC) filesAll.push_back(file); // Instances with n mod 8 = 4
    for(auto & file: filesD) filesAll.push_back(file); // Instances with n mod 8 = 6

	clock_t s_clock, t_clock;
	s_clock = clock();

	// read the design of left and last super-games
	FILE *fp=fopen("TTP//Design//Left_super_game.txt","r"); read_table_left_super_game(fp, total_number_left, left_super_game);
	fp=fopen("TTP//Design//Last_super_game.txt","r"); read_table_last_super_game(fp, total_number_last, last_super_game);
	
	// test all instances satisfying n mod 8 = 0
	for (int i=0; i<filesA.size(); i++) {

		string file = filesA[i];
        size_t s = file.find(".txt")-2;
        string result = file.substr(s, 2);
        int n = atoi(result.c_str());
        size_t start = file.find("Instance//");
        size_t end = file.find(".txt");
        string name = file.substr(start+10, end - start-10);

		// Our solution
		int solution=INT_MAX;

		ouralgorithm(file, n, solution);

		cout<<name<<"\t"<<solution<<endl;
	}
	t_clock = clock();
	printf("The running time is:%lf\n", double(t_clock-s_clock)/CLOCKS_PER_SEC);

	system("pause");
		
	return 0;
}
