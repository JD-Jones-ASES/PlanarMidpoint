# PlanarMidpoint

A Lean proof of the **dimension-two case of Nielsen–Okamura Conjecture 9.1**:
on a connected open subset of the Euclidean plane, complementary canonical
midpoints for a pair of dual torsion-free connections force their symmetric
cubic tensor to be constant.

The repository is private. It has not been submitted to or registered with
Palomar. The theorem concerns dimension two; it does not resolve the conjecture
in arbitrary dimension.

## Statements

Write a totally symmetric cubic tensor as its four coefficients
$C=(a,b,c,d)=(C_{111},C_{112},C_{122},C_{222})$. Raising an index with the
Euclidean metric gives the symmetric bilinear map

```math
K_C(u,v)=\bigl(a u_1v_1+b(u_1v_2+u_2v_1)+c u_2v_2,
 b u_1v_1+c(u_1v_2+u_2v_1)+d u_2v_2\bigr).
```

Thus $\langle K_C(u,v),w\rangle=C(u,v,w)$ and the dual connections are
$D+K_C$ and $D-K_C$. Total symmetry is built into these four coordinates;
the derivative of the field retains all eight independent entries.
`TensorSemantics.lean` proves that this representation exhausts symmetric
trilinear tensors on the Euclidean plane.

The independent, Mathlib-only statement file is
[`PlanarMidpointChallenge.lean`](PlanarMidpointChallenge.lean).
[`PlanarMidpointSolution.lean`](PlanarMidpointSolution.lean) imports the proofs.
The three Comparator entries are:

* `PlanarMidpoint.planar_dual_midpoint_rigidity`: a smooth field on an open
  preconnected domain is constant if the canonical local midpoint maps of
  $D+K_C$ and $D-K_C$ satisfy $A_+(P,Q)+A_-(P,Q)=P+Q$ near every diagonal point.
* `PlanarMidpoint.planar_obstruction_rigidity`: an everywhere Fréchet
  differentiable field on such a domain is constant if, at every point and in
  every direction $h$, the following expression vanishes, with $J=DC$:

```math
E(C,J;h)=2K_C\bigl(h,K_{Jh}(h,h)\bigr)
 +5K_{J(K_C(h,h))}(h,h)
 -4K_{Jh}\bigl(h,K_C(h,h)\bigr).
```

* `PlanarMidpoint.planar_five_direction_rigidity`: in the differential theorem,
  the five directions $h=(j,1)$ for $j=0,1,2,3,4$ suffice, at every spatial point.

The geometric proof in fact needs only $C^2$ regularity, as recorded by
`planar_midpoint_rigidity_C2`. Preconnectedness includes the empty domain,
where the constant-field conclusion is vacuous. Convexity is not assumed.

## Canonical midpoint meaning

`IsGeodesicSegment` uses genuine curves with
$\gamma'=v$ and $v'=-\sigma K_{C(\gamma)}(v,v)$ on $[0,1]$.
`IsCanonicalLocalMidpoint` requires prescribed endpoints, position and velocity
bounds near the diagonal, and uniqueness among these short curves; the midpoint
is $\gamma(1/2)$. Both signs use the same endpoint neighborhood. The neighborhood
and shortness radius may depend on the basepoint.

`exists_unique_short_geodesic` constructs this branch by a Banach contraction
with the Dirichlet Green operator. `exists_canonical_local_midpoint` proves
existence of the resulting germs, and `canonical_midpoint_germs_agree` proves
independence of the construction after shrinking the common neighborhood.
No endpoint smoothness or obstruction identity is assumed in the geometric
theorem. The short branch is the usual canonical local geodesic branch:
small initial-data geodesics lie in the short class, and uniqueness identifies
their midpoint germs.

## Proof

For endpoints $p\pm\varepsilon h/2$, an explicit fourth-order approximate
geodesic satisfies the endpoints exactly. Spatial $C^2$ Taylor estimates and a
quantitative Dirichlet stability estimate compare it with the actual short
geodesic. Exact polynomial identities give the sum of the two approximate
midpoints as $2p+\varepsilon^4E(C(p),DC(p);h)/192$. The error is
$o(\varepsilon^4)$. Exact complementarity therefore forces $E=0$.
The formal proof uses explicit norm bounds to make this limit argument;
it does not presume a smoothly parameterized family of boundary solutions.

Each component of $E$ is a homogeneous quartic in $h$. Its ten coefficients
form a linear system in the eight entries of $DC$. Exact polynomial
certificates show that a nonzero cubic with nontrivial kernel must belong
to one of two exceptional graphs. With $\tau=(a+c,b+d)=(s,t)\ne0$, these are

```math
Q(s,t)=\frac{(s^3,s^2t,st^2,t^3)}{s^2+t^2},\qquad
R(s,t)=(3s,t,s,3t)-3Q(s,t).
```

Both extend continuously by zero at the origin. Away from these graphs,
the linear system is injective. On either nonzero graph, separate exact
certificates show that the space of derivatives tangent to the graph
intersects the obstruction kernel only in zero. The normalizing coordinate change is fixed at a point; no
varying frame is differentiated as a constant. A relative clopen level-set
argument handles transitions and zero values on arbitrary connected open
domains using only differentiability. Finally, quartic interpolation yields
the five-direction criterion.

The finite certificates are ordinary Lean algebra proofs, not external
oracle calls or numerical tests. All proof dependencies use only
`propext`, `Quot.sound`, and `Classical.choice`. Deliberate `sorry` placeholders
occur only in the independent Challenge statement file.

## Reproduce

The committed `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` pin
Lean and every dependency. With Elan installed:

```sh
lake exe cache get
lake build
lake comparator --config comparator.json
```

Comparator requires Linux with bubblewrap. The private GitHub Actions workflow
builds the exact checked-out commit, audits the theorem axioms, compares all
three statements and definitions, and replays the exported proofs through
Lean, NanoDa and con-ron. A separate fresh-runner build checks reproducibility.
The runtime configuration enabling the extra kernels is generated in the
runner's temporary directory; the committed configuration follows Palomar's
statement format. These checks are private preparation, not registry intake.

## Sources and authorship

Frank Nielsen and Kazuki Okamura,
[arXiv:2609.07551v2, Section 9](https://arxiv.org/html/2609.07551v2#S9),
pose the conjecture and supply the midpoint-expansion framework and
constant-cubic sufficiency. This project proves planar necessity, including
the exceptional tensors, and strengthens the differential regularity.
The nearby [two-dimensional Matkowski–Sutô work](https://arxiv.org/html/2609.11102v1)
concerns coordinate generators and does not supply the Euclidean-dual theorem
proved here. No global priority or external peer-review claim is made.

JD Jones is the responsible human maintainer. OpenAI Codex agents developed
the mathematical argument, Lean proofs and verification tooling and performed
separate statement and axiom reviews. Structured provenance and automation
disclosure are in [`formalization.yaml`](formalization.yaml).
