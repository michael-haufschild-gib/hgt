import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# The tree-quotient black hole of an elliptic curve

For an elliptic curve `E/𝔽_q` with rational point `∞`, the quotient `Γ\T_∞` of the Bruhat–Tits tree by
`Γ = GL₂(𝔽_q[E - ∞])` is an explicit edge-indexed graph (Takahashi). Its vertices are the rank-two
bundles with fixed determinant up to `O(∞)`:

* the **core**: the stable bundle of odd degree;
* **dead ends**: the bundles descended from `𝔽_{q²}`, one for each `x ∈ ℙ¹(𝔽_q)` with no rational point
  above it;
* **necks**: `L ⊕ L⁻¹`, `L² ≠ O`, one for each pair `±P` of rational points. At a two-torsion point the
  neck is a **pin**, the nonsplit self-extension of `L`, and a **cap** `L ⊕ L` hangs behind it;
* **rays**: `L(k+1)∞ ⊕ L⁻¹`, one half-line for each rational point `P ∈ G = E(𝔽_q)`: the cusps.

The graph needs only `q`, the abelian group `G` and the dead ends `D`, subject to the local count
`#{±P} + #D = q + 1`. It makes sense for every such triple, whether or not a curve exists. This module
defines it, with its wave operator `A` and its unimodular measure, and proves Green's identity.

Every vertex has `q + 1` edges (`waveOp_one`), and the measure is balanced across edges, so by
Bass–Kulkarni the graph is the quotient of the `(q+1)`-regular tree by a lattice. All of this holds for
every such `(q, G, D)`, including data that no curve realizes.
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

/-- Points of `G` up to sign: the points of the `x`-line with a rational point above them. -/
def negSetoid (G : Type*) [AddCommGroup G] : Setoid G where
  r P Q := Q = P ∨ Q = -P
  iseqv :=
    ⟨fun _ => Or.inl rfl,
      fun {P Q} h => by rcases h with rfl | rfl <;> simp,
      fun {P Q R} h₁ h₂ => by rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp⟩

/-- The classes `{P, -P}`. -/
abbrev Branch (G : Type*) [AddCommGroup G] := Quotient (negSetoid G)

/-- The class of `P`. -/
def Branch.mk {G : Type*} [AddCommGroup G] (P : G) : Branch G := Quotient.mk (negSetoid G) P

theorem Branch.mk_neg {G : Type*} [AddCommGroup G] (P : G) : Branch.mk (-P) = Branch.mk P :=
  Quotient.sound (Or.inr (neg_neg P).symm)

/-- The two-torsion points: the labels of the caps. -/
abbrev TwoTorsion (G : Type*) [AddCommGroup G] := {P : G // 2 • P = 0}

/-- The vertices of the black hole. A neck at a two-torsion class is a pin. -/
inductive Vertex (G D : Type*) [AddCommGroup G]
  | core : Vertex G D
  | dead (d : D) : Vertex G D
  | neck (x : Branch G) : Vertex G D
  | cap (L : TwoTorsion G) : Vertex G D
  | ray (P : G) (k : ℕ) : Vertex G D

/-- The channel data of a black hole: the local count that makes every vertex have `q + 1` edges. -/
structure Channels (G D : Type*) [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype D] where
  q : ℕ
  two_le : 2 ≤ q
  count : Fintype.card (TwoTorsion G) + Fintype.card G + 2 * Fintype.card D = 2 * (q + 1)

variable {G D : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype D]

/-- The weight of `P` in a sum over classes: a class of two elements is counted by halves. -/
def branchWeight (P : G) : ℂ := if 2 • P = 0 then 1 else 1 / 2

theorem two_nsmul_neg_eq_zero_iff (P : G) : 2 • (-P) = 0 ↔ 2 • P = 0 := by
  rw [smul_neg, neg_eq_zero]

theorem branchWeight_neg (P : G) : branchWeight (-P) = branchWeight P := by
  simp only [branchWeight, two_nsmul_neg_eq_zero_iff]

/-- The wave operator at the neck of `P`. -/
def neckOp (q : ℕ) (f : Vertex G D → ℂ) (P : G) : ℂ :=
  if 2 • P = 0 then (q : ℂ) * f .core + f (.ray P 0)
  else ((q : ℂ) - 1) * f .core + f (.ray P 0) + f (.ray (-P) 0)

theorem neckOp_neg (q : ℕ) (f : Vertex G D → ℂ) (P : G) : neckOp q f (-P) = neckOp q f P := by
  unfold neckOp
  by_cases h : 2 • P = 0
  · have hP : -P = P := by
      have : P + P = 0 := by simpa [two_nsmul] using h
      exact neg_eq_of_add_eq_zero_left this
    rw [if_pos (by rwa [two_nsmul_neg_eq_zero_iff]), if_pos h, hP]
  · rw [if_neg h, if_neg (by rwa [two_nsmul_neg_eq_zero_iff]), neg_neg]
    ring

/-- The contribution of the gap-zero vertices to the wave operator at the root of the ray of `P`. -/
def gapOp (q : ℕ) (f : Vertex G D → ℂ) (P : G) : ℂ :=
  if h : 2 • P = 0 then ((q : ℂ) - 1) * f (.neck (Branch.mk P)) + f (.cap ⟨P, h⟩)
  else (q : ℂ) * f (.neck (Branch.mk P))

/-- The wave operator `A` of the black hole: `(A f)(v) = Σ_w i(v,w) f(w)`, the sum over the `q + 1` edges
at `v`. -/
def waveOp (q : ℕ) (f : Vertex G D → ℂ) : Vertex G D → ℂ
  | .core => ∑ d, f (.dead d) + ∑ P, branchWeight P * f (.neck (Branch.mk P))
  | .dead _ => ((q : ℂ) + 1) * f .core
  | .neck x =>
      Quotient.liftOn x (neckOp q f) (fun P Q h => by
        rcases h with rfl | rfl
        · rfl
        · exact (neckOp_neg q f P).symm)
  | .cap L => ((q : ℂ) + 1) * f (.ray L.1 0)
  | .ray P 0 => gapOp q f P + f (.ray P 1)
  | .ray P (k + 1) => (q : ℂ) * f (.ray P k) + f (.ray P (k + 2))

@[simp] theorem waveOp_core (q : ℕ) (f : Vertex G D → ℂ) :
    waveOp q f .core = ∑ d, f (.dead d) + ∑ P, branchWeight P * f (.neck (Branch.mk P)) := rfl

@[simp] theorem waveOp_dead (q : ℕ) (f : Vertex G D → ℂ) (d : D) :
    waveOp q f (.dead d) = ((q : ℂ) + 1) * f .core := rfl

@[simp] theorem waveOp_neck (q : ℕ) (f : Vertex G D → ℂ) (P : G) :
    waveOp q f (.neck (Branch.mk P)) = neckOp q f P := rfl

@[simp] theorem waveOp_cap (q : ℕ) (f : Vertex G D → ℂ) (L : TwoTorsion G) :
    waveOp q f (.cap L) = ((q : ℂ) + 1) * f (.ray L.1 0) := rfl

@[simp] theorem waveOp_ray_zero (q : ℕ) (f : Vertex G D → ℂ) (P : G) :
    waveOp q f (.ray P 0) = gapOp q f P + f (.ray P 1) := rfl

@[simp] theorem waveOp_ray_succ (q : ℕ) (f : Vertex G D → ℂ) (P : G) (k : ℕ) :
    waveOp q f (.ray P (k + 1)) = (q : ℂ) * f (.ray P k) + f (.ray P (k + 2)) := rfl

/-- `a`: the number of two-torsion points, in `ℂ`. -/
def torsionCount (G : Type*) [AddCommGroup G] [DecidableEq G] [Fintype G] : ℂ :=
  (Fintype.card (TwoTorsion G) : ℂ)

/-- `h`: the number of cusps, in `ℂ`. -/
def cuspCount (G : Type*) [Fintype G] : ℂ := (Fintype.card G : ℂ)

/-- A function of `P` that takes one value on two-torsion points and another off it. -/
theorem sum_ite_torsion (u v : ℂ) :
    ∑ P : G, (if 2 • P = 0 then u else v) =
      torsionCount G * u + (cuspCount G - torsionCount G) * v := by
  have hcard : ((univ.filter fun P : G => 2 • P = 0).card : ℂ) = torsionCount G := by
    unfold torsionCount
    rw [Fintype.card_subtype]
  have hcompl : (((univ.filter fun P : G => ¬ 2 • P = 0).card : ℕ) : ℂ) =
      cuspCount G - torsionCount G := by
    rw [← hcard, cuspCount, eq_sub_iff_add_eq, ← Nat.cast_add, add_comm,
      Finset.card_filter_add_card_filter_not, Finset.card_univ]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hcard, hcompl]

/-- The local count in `ℂ`: `a + h + 2c = 2(q+1)`. -/
theorem Channels.count_complex (B : Channels G D) :
    torsionCount G + cuspCount G + 2 * (Fintype.card D : ℂ) = 2 * ((B.q : ℂ) + 1) := by
  have := congrArg (Nat.cast : ℕ → ℂ) B.count
  push_cast at this
  simpa [torsionCount, cuspCount] using this

theorem Channels.q_ne_zero (B : Channels G D) : (B.q : ℂ) ≠ 0 := by
  have := B.two_le
  exact Nat.cast_ne_zero.mpr (by omega)

theorem Channels.q_sub_one_ne_zero (B : Channels G D) : (B.q : ℂ) - 1 ≠ 0 := by
  have := B.two_le
  intro h
  have h1 : (B.q : ℂ) = ((1 : ℕ) : ℂ) := by
    rw [Nat.cast_one]
    exact sub_eq_zero.mp h
  have h2 := Nat.cast_injective h1
  omega

theorem Channels.q_add_one_ne_zero (B : Channels G D) : (B.q : ℂ) + 1 ≠ 0 := by
  have h : ((B.q + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simpa using h

/-- **Local regularity.** The constant function is an eigenfunction with eigenvalue `q + 1`: every vertex
has `q + 1` edges. -/
theorem Channels.waveOp_one (B : Channels G D) (v : Vertex G D) :
    waveOp B.q (fun _ => (1 : ℂ)) v = (B.q : ℂ) + 1 := by
  have hweights : ∑ P : G, branchWeight P * (1 : ℂ) =
      torsionCount G + (cuspCount G - torsionCount G) * (1 / 2) := by
    simp only [branchWeight, mul_one]
    rw [sum_ite_torsion]
    ring
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · rw [waveOp_core, hweights]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    linear_combination (1 / 2 : ℂ) * B.count_complex
  · simp
  · induction x using Quotient.inductionOn with
    | h P =>
      change waveOp B.q (fun _ => (1 : ℂ)) (.neck (Branch.mk P)) = _
      rw [waveOp_neck]
      unfold neckOp
      split_ifs <;> ring
  · simp
  · rw [waveOp_ray_zero]
    unfold gapOp
    split_ifs <;> ring
  · simp

/-- The wave operator preserves nonnegativity: its coefficients are edge counts. -/
theorem waveOp_nonneg (q : ℕ) (hq : 1 ≤ q) {f : Vertex G D → ℝ} (hf : ∀ v, 0 ≤ f v) (v : Vertex G D) :
    ∃ r : ℝ, 0 ≤ r ∧ waveOp q (fun w => (f w : ℂ)) v = r := by
  have hq1 : (0 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · refine ⟨∑ d, f (.dead d) + ∑ P : G, (if 2 • P = 0 then 1 else 1 / 2) * f (.neck (Branch.mk P)),
      add_nonneg (Finset.sum_nonneg fun _ _ => hf _) (Finset.sum_nonneg fun P _ => ?_), ?_⟩
    · split_ifs
      · simpa using hf _
      · exact mul_nonneg (by norm_num) (hf _)
    · rw [waveOp_core]
      push_cast
      simp only [branchWeight]
      congr 1
      refine Finset.sum_congr rfl fun P _ => ?_
      split_ifs <;> simp
  · exact ⟨(q + 1) * f .core, mul_nonneg (by linarith) (hf _), by simp⟩
  · induction x using Quotient.inductionOn with
    | h P =>
      change ∃ r : ℝ, 0 ≤ r ∧ waveOp q (fun w => (f w : ℂ)) (.neck (Branch.mk P)) = r
      rw [waveOp_neck]
      unfold neckOp
      split_ifs
      · exact ⟨q * f .core + f (.ray P 0), add_nonneg (mul_nonneg hq0 (hf _)) (hf _), by simp⟩
      · refine ⟨(q - 1) * f .core + f (.ray P 0) + f (.ray (-P) 0),
          add_nonneg (add_nonneg (mul_nonneg hq1 (hf _)) (hf _)) (hf _), by simp⟩
  · exact ⟨(q + 1) * f (.ray L.1 0), mul_nonneg (by linarith) (hf _), by simp⟩
  · rw [waveOp_ray_zero]
    unfold gapOp
    split_ifs with h
    · exact ⟨(q - 1) * f (.neck (Branch.mk P)) + f (.cap ⟨P, h⟩) + f (.ray P 1),
        add_nonneg (add_nonneg (mul_nonneg hq1 (hf _)) (hf _)) (hf _), by simp⟩
    · exact ⟨q * f (.neck (Branch.mk P)) + f (.ray P 1),
        add_nonneg (mul_nonneg hq0 (hf _)) (hf _), by simp⟩
  · exact ⟨q * f (.ray P k) + f (.ray P (k + 2)), add_nonneg (mul_nonneg hq0 (hf _)) (hf _), by simp⟩

/-! ### The measure and Green's identity -/

/-- The mass of the root of a ray, shifted: `μ_k = 1/((q-1) q^{k+1})`. -/
def rayMass (q : ℕ) (k : ℕ) : ℂ := 1 / (((q : ℂ) - 1) * (q : ℂ) ^ (k + 1))

/-- The mass of the neck of `P`. -/
def neckMass (q : ℕ) (P : G) : ℂ := if 2 • P = 0 then 1 / (q : ℂ) else 1 / ((q : ℂ) - 1)

theorem neckMass_neg (q : ℕ) (P : G) : neckMass q (-P) = neckMass q P := by
  simp only [neckMass, two_nsmul_neg_eq_zero_iff]

/-- The invariant measure: `μ(v)` is the reciprocal of the stabilizer order, up to `q - 1`. -/
def mass (q : ℕ) : Vertex G D → ℂ
  | .core => 1
  | .dead _ => 1 / ((q : ℂ) + 1)
  | .neck x => Quotient.liftOn x (neckMass q) (fun P Q h => by
      rcases h with rfl | rfl
      · rfl
      · exact (neckMass_neg q P).symm)
  | .cap _ => 1 / (((q : ℂ) ^ 2 - 1) * q)
  | .ray _ k => rayMass q k

@[simp] theorem mass_core (q : ℕ) : mass q (.core : Vertex G D) = 1 := rfl
@[simp] theorem mass_dead (q : ℕ) (d : D) : mass q (.dead d : Vertex G D) = 1 / ((q : ℂ) + 1) := rfl
@[simp] theorem mass_neck (q : ℕ) (P : G) :
    mass q (.neck (Branch.mk P) : Vertex G D) = neckMass q P := rfl
@[simp] theorem mass_cap (q : ℕ) (L : TwoTorsion G) :
    mass q (.cap L : Vertex G D) = 1 / (((q : ℂ) ^ 2 - 1) * q) := rfl
@[simp] theorem mass_ray (q : ℕ) (P : G) (k : ℕ) :
    mass q (.ray P k : Vertex G D) = rayMass q k := rfl

/-- The sum of `F` over the part of the graph below depth `K`. Classes `{P, -P}` are summed by halves. -/
def truncSum (K : ℕ) (F : Vertex G D → ℂ) : ℂ :=
  F .core + ∑ d, F (.dead d) + ∑ P : G, branchWeight P * F (.neck (Branch.mk P)) +
    ∑ P : G, (if h : 2 • P = 0 then F (.cap ⟨P, h⟩) else 0) +
    ∑ P : G, ∑ k ∈ range K, F (.ray P k)

/-- The boundary term of Green's identity on one ray, between depths `K` and `K + 1`. -/
def rayFlux (q : ℕ) (f g : Vertex G D → ℂ) (P : G) (K : ℕ) : ℂ :=
  rayMass q K * (f (.ray P (K + 1)) * g (.ray P K) - f (.ray P K) * g (.ray P (K + 1)))

/-- The integrand of Green's identity. -/
def greenDensity (q : ℕ) (f g : Vertex G D → ℂ) (v : Vertex G D) : ℂ :=
  mass q v * (waveOp q f v * g v - f v * waveOp q g v)

/-- `q · μ_{k+1} = μ_k`: the balance of the measure along a ray. -/
theorem rayMass_succ_mul {q : ℕ} (hq : (q : ℂ) ≠ 0) (k : ℕ) :
    rayMass q (k + 1) * q = rayMass q k := by
  unfold rayMass
  by_cases h1 : (q : ℂ) - 1 = 0
  · simp [h1]
  · field_simp
    ring

/-- The transfer term between a neck and one of its rays. It cancels in pairs under `P ↦ -P`. -/
def neckTransfer (q : ℕ) (f g : Vertex G D → ℂ) (P : G) : ℂ :=
  if 2 • P = 0 then 0
  else (1 / ((q : ℂ) - 1)) * (f (.ray P 0) * g (.neck (Branch.mk P)) -
    f (.neck (Branch.mk P)) * g (.ray P 0))

/-- The per-point form of Green's identity at gap zero. -/
theorem green_per_point (B : Channels G D) (f g : Vertex G D → ℂ) (P : G) :
    branchWeight P * (f (.neck (Branch.mk P)) * g .core - f .core * g (.neck (Branch.mk P))) +
        branchWeight P * greenDensity B.q f g (.neck (Branch.mk P)) +
        (if h : 2 • P = 0 then greenDensity B.q f g (.cap ⟨P, h⟩) else 0) +
        greenDensity B.q f g (.ray P 0) =
      rayFlux B.q f g P 0 + (1 / 2) * neckTransfer B.q f g (-P) -
        (1 / 2) * neckTransfer B.q f g P := by
  have hq := B.q_ne_zero
  have hq1 := B.q_sub_one_ne_zero
  have hq2 := B.q_add_one_ne_zero
  have hsq : (B.q : ℂ) ^ 2 - 1 ≠ 0 := by
    have : (B.q : ℂ) ^ 2 - 1 = ((B.q : ℂ) - 1) * ((B.q : ℂ) + 1) := by ring
    rw [this]
    exact mul_ne_zero hq1 hq2
  unfold greenDensity rayFlux neckTransfer
  simp only [mass_neck, mass_ray, waveOp_neck, waveOp_ray_zero, mass_cap, waveOp_cap]
  unfold neckOp gapOp neckMass branchWeight rayMass
  by_cases h : 2 • P = 0
  · have hP : -P = P := by
      have : P + P = 0 := by simpa [two_nsmul] using h
      exact neg_eq_of_add_eq_zero_left this
    simp only [h, dif_pos, if_true, hP]
    field_simp
    ring
  · have h' : ¬ 2 • (-P) = 0 := by rwa [two_nsmul_neg_eq_zero_iff]
    simp only [h, h', dif_neg, if_false, not_false_eq_true, Branch.mk_neg]
    field_simp
    ring

/-- **Green's identity (the flux law).** For all `f`, `g`, the sum of `μ·((Af)g - f(Ag))` below depth
`K + 1` is the sum of the boundary terms on the rays between depths `K` and `K + 1`. There is no other
boundary: this is Maass–Selberg on the graph. -/
theorem truncSum_greenDensity (B : Channels G D) (f g : Vertex G D → ℂ) (K : ℕ) :
    truncSum (K + 1) (greenDensity B.q f g) = ∑ P : G, rayFlux B.q f g P K := by
  have hq := B.q_ne_zero
  have hq1 := B.q_sub_one_ne_zero
  have hq2 := B.q_add_one_ne_zero
  induction K with
  | zero =>
    have hcore : greenDensity B.q f g .core =
        ∑ d, (f (.dead d) * g .core - f .core * g (.dead d)) +
          ∑ P : G, branchWeight P * (f (.neck (Branch.mk P)) * g .core -
            f .core * g (.neck (Branch.mk P))) := by
      unfold greenDensity
      simp only [mass_core, waveOp_core, one_mul, Finset.sum_sub_distrib, mul_sub,
        Finset.mul_sum, Finset.sum_mul, add_mul, mul_add]
      have e1 : ∀ P : G, f .core * (branchWeight P * g (.neck (Branch.mk P))) =
          branchWeight P * (f .core * g (.neck (Branch.mk P))) := fun P => by ring
      have e2 : ∀ P : G, branchWeight P * f (.neck (Branch.mk P)) * g .core =
          branchWeight P * (f (.neck (Branch.mk P)) * g .core) := fun P => by ring
      simp only [e1, e2]
      ring
    have hdead : ∀ d : D, greenDensity B.q f g (.dead d) =
        f .core * g (.dead d) - f (.dead d) * g .core := by
      intro d
      unfold greenDensity
      simp only [mass_dead, waveOp_dead]
      field_simp
    have hdsum : ∑ d, greenDensity B.q f g (.dead d) +
        ∑ d, (f (.dead d) * g .core - f .core * g (.dead d)) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [hdead]
      ring
    have hper := Finset.sum_congr (rfl : (univ : Finset G) = univ)
      (fun P _ => green_per_point B f g P)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hper
    have hswap : ∑ P : G, (1 / 2 : ℂ) * neckTransfer B.q f g (-P) =
        ∑ P : G, (1 / 2 : ℂ) * neckTransfer B.q f g P :=
      Equiv.sum_comp (Equiv.neg G) (fun P => (1 / 2 : ℂ) * neckTransfer B.q f g P)
    unfold truncSum
    simp only [Finset.sum_range_one, zero_add]
    rw [hcore]
    linear_combination hper + hdsum + hswap
  | succ K ih =>
    have hstep : truncSum (K + 1 + 1) (greenDensity B.q f g) =
        truncSum (K + 1) (greenDensity B.q f g) +
          ∑ P : G, greenDensity B.q f g (.ray P (K + 1)) := by
      unfold truncSum
      simp only [Finset.sum_range_succ _ (K + 1), Finset.sum_add_distrib]
      ring
    have hray : ∀ P : G, greenDensity B.q f g (.ray P (K + 1)) =
        rayFlux B.q f g P (K + 1) - rayFlux B.q f g P K := by
      intro P
      unfold greenDensity rayFlux
      simp only [mass_ray, waveOp_ray_succ]
      have hm := rayMass_succ_mul hq K
      linear_combination
        (f (.ray P K) * g (.ray P (K + 1)) - f (.ray P (K + 1)) * g (.ray P K)) * hm
    rw [hstep, ih, Finset.sum_congr rfl fun P _ => hray P, Finset.sum_sub_distrib]
    ring

end GaloisForLFunctions.ArithmeticScatteringHolography

end
