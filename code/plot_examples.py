#!/usr/bin/env python3
"""Optional preview renderer; requires matplotlib. Core graph code does not."""
from math import cos, sin, pi
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, Circle
from cyclic_tournaments import CyclicTournament


def main():
    specifications = [
        ("Directed triangle", 3, {1}, 3),
        ("Consecutive connectors", 5, {1,2}, 5),
        ("Paley tournament", 7, {1,2,4}, 21),
        ("Three triangles in a cycle", 9, {1,3,4,7}, 81),
    ]
    fig, axes = plt.subplots(2,2,figsize=(11,12))
    fig.patch.set_facecolor("white")
    for ax,(title,n,s,order) in zip(axes.flat,specifications):
        t = CyclicTournament(n,frozenset(s))
        positions = [(cos(pi/2-2*pi*v/n), sin(pi/2-2*pi*v/n)) for v in range(n)]
        for u,v in t.arcs:
            arrow = FancyArrowPatch(positions[u],positions[v],arrowstyle="-|>",
                                    mutation_scale=9,linewidth=0.8,color="#586474",alpha=0.72,
                                    shrinkA=18,shrinkB=18,zorder=1)
            ax.add_patch(arrow)
        for v,(x,y) in enumerate(positions):
            color = "#f6b95d" if t.canonical_coloring[v]==1 else "#8fc4ea"
            ax.add_patch(Circle((x,y),0.093,facecolor=color,edgecolor="#142e47",lw=1.2,zorder=2))
            ax.text(x,y,str(v),ha="center",va="center",fontsize=12,color="#142e47",zorder=3)
        ax.set_aspect("equal")
        ax.set_xlim(-1.25,1.25)
        ax.set_ylim(-1.33,1.25)
        ax.axis("off")
        ax.set_title(title+f" ($n={n}$)",fontsize=15,fontweight="bold",color="#142e47",pad=9)
        ax.text(0,-1.20,"S = {"+", ".join(map(str,sorted(s)))+"}",ha="center",fontsize=11,color="#354658")
        ax.text(0,-1.34,f"Automorphisms: {order} before labels; 1 after labels",ha="center",fontsize=10,color="#354658")
    fig.suptitle("The same half-interval labeling breaks every symmetry",fontsize=19,fontweight="bold",color="#142e47",y=0.975)
    fig.text(0.5,0.942,"Orange: 0 through floor(n/2)     Blue: remaining vertices",ha="center",fontsize=12,color="#354658")
    fig.subplots_adjust(top=0.91,bottom=0.045,hspace=0.28,wspace=0.15)
    out = Path(__file__).resolve().parents[1]/"graphs"/"examples_overview.png"
    fig.savefig(out,dpi=180,facecolor="white")
    plt.close(fig)
    print(out)


if __name__ == "__main__":
    main()
