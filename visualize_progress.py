#!/usr/bin/env python3
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
import seaborn as sns

# Set style
plt.style.use('seaborn-v0_8-darkgrid')
sns.set_palette("husl")

# Data from analysis
modules = [
    'PNT1_ComplexAnalysis',
    'PNT2_LogDerivative',
    'PNT3_RiemannZeta',
    'PNT4_ZeroFreeRegion',
    'PNT5_StrongPNT'
]

proven = [215, 79, 53, 88, 21]
sorries = [34, 35, 33, 41, 21]
total = [p + s for p, s in zip(proven, sorries)]
completion_pct = [p * 100 / t for p, t in zip(proven, total)]

# Create figure with subplots
fig = plt.figure(figsize=(15, 10))

# 1. Stacked bar chart showing proven vs sorries
ax1 = plt.subplot(2, 2, 1)
x = np.arange(len(modules))
width = 0.6

bars1 = ax1.bar(x, proven, width, label='Proven', color='#2ecc71')
bars2 = ax1.bar(x, sorries, width, bottom=proven, label='Sorries', color='#e74c3c')

ax1.set_ylabel('Number of Theorems/Lemmas')
ax1.set_title('Project Progress by Module')
ax1.set_xticks(x)
ax1.set_xticklabels([m.replace('PNT', '').replace('_', '\n') for m in modules], rotation=0)
ax1.legend()

# Add percentage labels on bars
for i, (p, s, t) in enumerate(zip(proven, sorries, total)):
    ax1.text(i, t + 5, f'{completion_pct[i]:.0f}%', ha='center', fontweight='bold')

# 2. Pie chart of overall progress
ax2 = plt.subplot(2, 2, 2)
total_proven = sum(proven)
total_sorries = sum(sorries)
colors = ['#2ecc71', '#e74c3c']
sizes = [total_proven, total_sorries]
explode = (0.05, 0)

wedges, texts, autotexts = ax2.pie(sizes, explode=explode, labels=['Proven', 'Sorries'],
                                    colors=colors, autopct='%1.1f%%', startangle=90)
ax2.set_title('Overall Project Completion')

# Make percentage text bold
for autotext in autotexts:
    autotext.set_fontweight('bold')
    autotext.set_fontsize(12)

# 3. Progress over time (sorry count)
ax3 = plt.subplot(2, 2, 3)
# Recent sorry counts from git history
dates = ['Initial', 'Week 1', 'Week 2', 'Current']
sorry_counts = [180, 170, 165, 164]

ax3.plot(dates, sorry_counts, 'o-', linewidth=2, markersize=8, color='#3498db')
ax3.set_ylabel('Number of Sorries')
ax3.set_title('Sorry Count Reduction Over Time')
ax3.set_ylim(160, 185)
ax3.grid(True, alpha=0.3)

# Add value labels
for i, (d, s) in enumerate(zip(dates, sorry_counts)):
    ax3.text(i, s + 1, str(s), ha='center', fontweight='bold')

# 4. Completion percentage by module (horizontal bar)
ax4 = plt.subplot(2, 2, 4)
y_pos = np.arange(len(modules))
colors_bar = ['#2ecc71' if c >= 70 else '#f39c12' if c >= 60 else '#e74c3c'
              for c in completion_pct]

bars = ax4.barh(y_pos, completion_pct, color=colors_bar)
ax4.set_yticks(y_pos)
ax4.set_yticklabels([m.replace('PNT', '').replace('_', ' ') for m in modules])
ax4.set_xlabel('Completion Percentage (%)')
ax4.set_title('Module Completion Status')
ax4.set_xlim(0, 100)

# Add percentage labels
for i, (bar, pct) in enumerate(zip(bars, completion_pct)):
    ax4.text(pct + 2, bar.get_y() + bar.get_height()/2,
             f'{pct:.1f}%', va='center', fontweight='bold')

# Add vertical lines for reference
ax4.axvline(x=50, color='gray', linestyle='--', alpha=0.5)
ax4.axvline(x=75, color='gray', linestyle='--', alpha=0.5)

plt.suptitle('Strong Prime Number Theorem - Project Progress Analysis',
             fontsize=16, fontweight='bold', y=0.98)
plt.tight_layout()

# Save the figure
plt.savefig('pnt_progress_visualization.png', dpi=150, bbox_inches='tight')
print("Visualization saved as pnt_progress_visualization.png")

# Create a second figure showing the proof dependency structure
fig2, ax = plt.subplots(figsize=(12, 8))

# Module dependencies (simplified)
dependencies = {
    'PNT1\nComplex\nAnalysis': [],
    'PNT2\nLog\nDerivative': ['PNT1\nComplex\nAnalysis'],
    'PNT3\nRiemann\nZeta': ['PNT1\nComplex\nAnalysis'],
    'PNT4\nZero-Free\nRegion': ['PNT3\nRiemann\nZeta', 'PNT2\nLog\nDerivative'],
    'PNT5\nStrong\nPNT': ['PNT4\nZero-Free\nRegion', 'PNT3\nRiemann\nZeta']
}

# Position nodes
positions = {
    'PNT1\nComplex\nAnalysis': (1, 2),
    'PNT2\nLog\nDerivative': (0, 1),
    'PNT3\nRiemann\nZeta': (2, 1),
    'PNT4\nZero-Free\nRegion': (1, 0.5),
    'PNT5\nStrong\nPNT': (1, 0)
}

# Completion percentages for coloring
node_colors = {
    'PNT1\nComplex\nAnalysis': 86,
    'PNT2\nLog\nDerivative': 69,
    'PNT3\nRiemann\nZeta': 62,
    'PNT4\nZero-Free\nRegion': 68,
    'PNT5\nStrong\nPNT': 50
}

# Draw edges (dependencies)
for node, deps in dependencies.items():
    for dep in deps:
        x1, y1 = positions[dep]
        x2, y2 = positions[node]
        ax.arrow(x1, y1, x2-x1, y2-y1, head_width=0.03, head_length=0.03,
                fc='gray', ec='gray', alpha=0.5, length_includes_head=True)

# Draw nodes
for node, (x, y) in positions.items():
    completion = node_colors[node]
    if completion >= 70:
        color = '#2ecc71'
    elif completion >= 60:
        color = '#f39c12'
    else:
        color = '#e74c3c'

    circle = plt.Circle((x, y), 0.15, color=color, ec='black', linewidth=2)
    ax.add_patch(circle)
    ax.text(x, y, node, ha='center', va='center', fontweight='bold', fontsize=9)
    ax.text(x, y-0.25, f'{completion}%', ha='center', va='center', fontsize=8)

ax.set_xlim(-0.5, 2.5)
ax.set_ylim(-0.5, 2.5)
ax.set_aspect('equal')
ax.axis('off')
ax.set_title('Module Dependency Graph\n(Color indicates completion: Green >70%, Yellow 60-70%, Red <60%)',
            fontsize=14, fontweight='bold', pad=20)

# Add legend
green_patch = mpatches.Patch(color='#2ecc71', label='>70% Complete')
yellow_patch = mpatches.Patch(color='#f39c12', label='60-70% Complete')
red_patch = mpatches.Patch(color='#e74c3c', label='<60% Complete')
ax.legend(handles=[green_patch, yellow_patch, red_patch], loc='upper right')

plt.tight_layout()
plt.savefig('pnt_dependency_graph.png', dpi=150, bbox_inches='tight')
print("Dependency graph saved as pnt_dependency_graph.png")

plt.show()