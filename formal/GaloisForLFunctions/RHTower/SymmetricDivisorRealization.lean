/-
# The FE + Schwarz class realizes every finite symmetric divisor: no local obstruction

The functional-equation and Schwarz-symmetric carriers (`FESchwarz`: differentiable with
`f(1−s) = f(s)` and `f(s̄) = \overline{f(s)}`) form a class closed under multiplication and
powers (`FESchwarz.mul`, `FESchwarz.pow`, `FESchwarz.finsetProd`).  Three symmetric building
blocks live inside it, each contributing a **simple** zero at a prescribed symmetric point:

* the `V₄`-orbit quartic `orbitQuartic ρ₀`, a simple zero at an off-line off-real `ρ₀`;
* the **crease pair** `linePair τ = (s − (½+iτ))(s − (½−iτ))`, a simple zero on the critical
  line at `½+iτ` (`τ ≠ 0`);
* the **real pair** `realPair r = (s − r)(s − (1−r))`, a simple zero at a real off-line `r ≠ ½`.

Both crease and real pairs are FE- and Schwarz-symmetric because they are monic quadratics with
**real coefficients** whose two roots are an `s ↦ 1−s` orbit: `linePair τ s = s² − s + (¼+τ²)`,
`realPair r s = s² − s + r(1−r)`.

The packing theorem `no_local_packing_obstruction` assembles these: given any finite family of
symmetric base blocks that each have a simple zero at its own point and are non-vanishing at every
other point, the product of their prescribed powers is again `FESchwarz` and has *exactly* the
prescribed vanishing order at each point — order is additive over the product and only the diagonal
block contributes.  Its concrete instantiation `symmetric_divisor_realizable` prescribes arbitrary
orders at an arbitrary finite configuration of generic, crease, and real points simultaneously.

Consequence: the FE + Schwarz class realizes every finite symmetric divisor exactly.  The
equivariant cylinder-packing problem therefore has **no local obstruction** — flat symmetry places
no constraint on which symmetric divisors are attainable.  Any packing constraint that binds the
defects of a completed member must carry hypotheses beyond flat symmetry; the obstruction, if any,
is arithmetic.
-/
import GaloisForLFunctions.RHTower.GoldilocksTrichotomy

noncomputable section

namespace RHTower

open Complex

/-! ### §1 Closure of the FE + Schwarz class under multiplication and powers -/

/-- The constant `1` is FE- and Schwarz-symmetric. -/
theorem fESchwarz_one : FESchwarz (fun _ => (1 : ℂ)) := by
  refine ⟨differentiable_const 1, fun s => rfl, fun s => ?_⟩
  simp

/-- The FE + Schwarz class is closed under pointwise multiplication: the functional equation and
Schwarz reflection distribute over a product. -/
theorem FESchwarz.mul {f g : ℂ → ℂ} (hf : FESchwarz f) (hg : FESchwarz g) :
    FESchwarz (fun s => f s * g s) := by
  obtain ⟨hfd, hffe, hfc⟩ := hf
  obtain ⟨hgd, hgfe, hgc⟩ := hg
  refine ⟨hfd.mul hgd, fun s => ?_, fun s => ?_⟩
  · show f (1 - s) * g (1 - s) = f s * g s
    rw [hffe, hgfe]
  · show f (starRingEnd ℂ s) * g (starRingEnd ℂ s) = starRingEnd ℂ (f s * g s)
    rw [hfc, hgc, map_mul]

/-- The FE + Schwarz class is closed under taking natural powers. -/
theorem FESchwarz.pow {f : ℂ → ℂ} (hf : FESchwarz f) (n : ℕ) :
    FESchwarz (fun s => (f s) ^ n) := by
  induction n with
  | zero =>
    have heq : (fun s => (f s) ^ 0) = (fun _ => (1 : ℂ)) := by funext s; rw [pow_zero]
    rw [heq]; exact fESchwarz_one
  | succ k ih =>
    have heq : (fun s => (f s) ^ (k + 1)) = (fun s => (f s) ^ k * f s) := by
      funext s; rw [pow_succ]
    rw [heq]; exact ih.mul hf

/-- The `V₄`-orbit quartic is FE- and Schwarz-symmetric. -/
theorem fESchwarz_orbitQuartic (ρ₀ : ℂ) : FESchwarz (orbitQuartic ρ₀) :=
  ⟨orbitQuartic_differentiable ρ₀, orbitQuartic_fe ρ₀, orbitQuartic_conj ρ₀⟩

/-- A finite product of FE + Schwarz members is FE + Schwarz. -/
theorem FESchwarz.finsetProd {ι : Type*} (t : Finset ι) (g : ι → ℂ → ℂ)
    (hg : ∀ i ∈ t, FESchwarz (g i)) : FESchwarz (fun s => ∏ i ∈ t, g i s) := by
  classical
  revert hg
  induction t using Finset.induction with
  | empty =>
    intro _
    have heq : (fun s : ℂ => ∏ i ∈ (∅ : Finset ι), g i s) = (fun _ => (1 : ℂ)) := by
      funext s; simp only [Finset.prod_empty]
    rw [heq]; exact fESchwarz_one
  | insert a t ha ih =>
    intro hg
    have hstep : (fun s => ∏ i ∈ insert a t, g i s) = (fun s => g a s * ∏ i ∈ t, g i s) := by
      funext s; simp only [Finset.prod_insert ha]
    rw [hstep]
    exact (hg a (Finset.mem_insert_self a t)).mul
      (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)))

/-! ### §1′ Additivity of the vanishing order over a finite product -/

/-- The vanishing order of a finite product of functions, each analytic at the point, is the sum of
their vanishing orders. -/
theorem analyticOrderAt_finsetProd {ι : Type*} (z : ℂ) (t : Finset ι) (g : ι → ℂ → ℂ)
    (hg : ∀ i ∈ t, AnalyticAt ℂ (g i) z) :
    analyticOrderAt (fun s => ∏ i ∈ t, g i s) z = ∑ i ∈ t, analyticOrderAt (g i) z := by
  classical
  revert hg
  induction t using Finset.induction with
  | empty =>
    intro _
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact analyticOrderAt_eq_zero.mpr (Or.inr one_ne_zero)
  | insert a t ha ih =>
    intro hg
    have han_a : AnalyticAt ℂ (g a) z := hg a (Finset.mem_insert_self a t)
    have han_rest : AnalyticAt ℂ (fun s => ∏ i ∈ t, g i s) z := by
      have h := Finset.analyticAt_prod (𝕜 := ℂ) t (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      have heq : (∏ i ∈ t, g i) = (fun s => ∏ i ∈ t, g i s) := by
        funext s; rw [Finset.prod_apply]
      rwa [heq] at h
    have hstep : (fun s => ∏ i ∈ insert a t, g i s) = (g a) * (fun s => ∏ i ∈ t, g i s) := by
      funext s; simp only [Pi.mul_apply, Finset.prod_insert ha]
    rw [hstep, analyticOrderAt_mul han_a han_rest, Finset.sum_insert ha,
        ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

/-- **The diagonal computation.**  A product of prescribed powers of blocks, where the distinguished
block `a` has a simple zero at `z` and every other block is non-vanishing at `z`, has vanishing order
exactly `mm a` at `z`. -/
theorem analyticOrderAt_prodPow_at {ι : Type*} (S : Finset ι) (blk : ι → ℂ → ℂ) (mm : ι → ℕ)
    (z : ℂ) (a : ι) (ha : a ∈ S)
    (hAn : ∀ i ∈ S, AnalyticAt ℂ (blk i) z)
    (hord_a : analyticOrderAt (blk a) z = 1)
    (hoth : ∀ i ∈ S, i ≠ a → blk i z ≠ 0) :
    analyticOrderAt (fun s => ∏ i ∈ S, (blk i s) ^ (mm i)) z = (mm a : ℕ∞) := by
  classical
  have hprod : analyticOrderAt (fun s => ∏ i ∈ S, (blk i s) ^ (mm i)) z
      = ∑ i ∈ S, analyticOrderAt (fun s => (blk i s) ^ (mm i)) z := by
    refine analyticOrderAt_finsetProd z S (fun i s => (blk i s) ^ (mm i)) ?_
    intro i hi
    show AnalyticAt ℂ (fun s => (blk i s) ^ (mm i)) z
    have hbridge : (fun s => (blk i s) ^ (mm i)) = (blk i) ^ (mm i) := by
      funext s; rw [Pi.pow_apply]
    rw [hbridge]; exact (hAn i hi).pow (mm i)
  have hterm : ∀ i ∈ S, analyticOrderAt (fun s => (blk i s) ^ (mm i)) z
      = (mm i) • analyticOrderAt (blk i) z := by
    intro i hi
    have hbridge : (fun s => (blk i s) ^ (mm i)) = (blk i) ^ (mm i) := by
      funext s; rw [Pi.pow_apply]
    rw [hbridge, analyticOrderAt_pow (hAn i hi)]
  have h0 : ∀ i ∈ S, i ≠ a → (mm i) • analyticOrderAt (blk i) z = 0 := by
    intro i hi hia
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (hoth i hi hia)), smul_zero]
  have h1 : a ∉ S → (mm a) • analyticOrderAt (blk a) z = 0 := fun h => absurd ha h
  rw [hprod, Finset.sum_congr rfl hterm, Finset.sum_eq_single a h0 h1, hord_a,
      nsmul_eq_mul, mul_one]

/-- A product of prescribed powers of blocks, all non-vanishing at `z`, is itself non-vanishing there,
so its vanishing order at `z` is `0`. -/
theorem analyticOrderAt_prodPow_zero {ι : Type*} (S : Finset ι) (blk : ι → ℂ → ℂ) (mm : ι → ℕ)
    (z : ℂ) (hnz : ∀ i ∈ S, blk i z ≠ 0) :
    analyticOrderAt (fun s => ∏ i ∈ S, (blk i s) ^ (mm i)) z = 0 := by
  classical
  refine analyticOrderAt_eq_zero.mpr (Or.inr ?_)
  show (∏ i ∈ S, (blk i z) ^ (mm i)) ≠ 0
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  exact pow_ne_zero (mm i) (hnz i hi)

/-! ### §2 Two new symmetric blocks: the crease pair and the real pair -/

/-- The **crease pair** at height `τ`: the monic quadratic with the conjugate roots `½ ± iτ` on the
critical line. -/
def linePair (τ : ℝ) : ℂ → ℂ :=
  fun s => (s - ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I)) * (s - ((1 / 2 : ℂ) - (τ : ℂ) * Complex.I))

/-- The crease pair in real-coefficient normal form: `linePair τ s = s² − s + (¼ + τ²)`. -/
theorem linePair_eq (τ : ℝ) (s : ℂ) :
    linePair τ s = s ^ 2 - s + ((1 / 4 + τ ^ 2 : ℝ) : ℂ) := by
  simp only [linePair]
  push_cast
  linear_combination (-(τ : ℂ) ^ 2) * Complex.I_sq

/-- The crease pair is FE- and Schwarz-symmetric: its roots are an `s ↦ 1−s` orbit and its
coefficients are real. -/
theorem fESchwarz_linePair (τ : ℝ) : FESchwarz (linePair τ) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold linePair; fun_prop
  · intro s; rw [linePair_eq, linePair_eq]; ring
  · intro s
    rw [linePair_eq, linePair_eq, map_add, map_sub, map_pow, Complex.conj_ofReal]

/-- The crease pair has a **simple** zero at its critical-line root `½ + iτ` (for `τ ≠ 0`): the
second factor there equals `2iτ ≠ 0`. -/
theorem linePair_order {τ : ℝ} (hτ : τ ≠ 0) :
    analyticOrderAt (linePair τ) ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) = 1 := by
  have hfeq : linePair τ = (fun s => s - ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I))
      * (fun s => s - ((1 / 2 : ℂ) - (τ : ℂ) * Complex.I)) := by
    funext s; simp only [linePair, Pi.mul_apply]
  have hlin_an : AnalyticAt ℂ (fun s : ℂ => s - ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I))
      ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) := analyticAt_id.sub analyticAt_const
  have hg_an : AnalyticAt ℂ (fun s : ℂ => s - ((1 / 2 : ℂ) - (τ : ℂ) * Complex.I))
      ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) := analyticAt_id.sub analyticAt_const
  have hg0 : ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) - ((1 / 2 : ℂ) - (τ : ℂ) * Complex.I) ≠ 0 := by
    have h1 : ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) - ((1 / 2 : ℂ) - (τ : ℂ) * Complex.I)
        = 2 * (τ : ℂ) * Complex.I := by ring
    rw [h1]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hτ)) Complex.I_ne_zero
  have hord_lin : analyticOrderAt (fun s : ℂ => s - ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I))
      ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) = 1 := analyticOrderAt_linGap_self _
  have hord_g : analyticOrderAt (fun s : ℂ => s - ((1 / 2 : ℂ) - (τ : ℂ) * Complex.I))
      ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hg0)
  rw [hfeq, analyticOrderAt_mul hlin_an hg_an, hord_lin, hord_g, add_zero]

/-- The **real pair** at `r`: the monic quadratic with the reflected real roots `r` and `1−r`. -/
def realPair (r : ℝ) : ℂ → ℂ :=
  fun s => (s - (r : ℂ)) * (s - ((1 - r : ℝ) : ℂ))

/-- The real pair in real-coefficient normal form: `realPair r s = s² − s + r(1−r)`. -/
theorem realPair_eq (r : ℝ) (s : ℂ) :
    realPair r s = s ^ 2 - s + ((r * (1 - r) : ℝ) : ℂ) := by
  simp only [realPair]; push_cast; ring

/-- The real pair is FE- and Schwarz-symmetric: its roots are an `s ↦ 1−s` orbit and its
coefficients are real. -/
theorem fESchwarz_realPair (r : ℝ) : FESchwarz (realPair r) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold realPair; fun_prop
  · intro s; rw [realPair_eq, realPair_eq]; ring
  · intro s
    rw [realPair_eq, realPair_eq, map_add, map_sub, map_pow, Complex.conj_ofReal]

/-- The real pair has a **simple** zero at its root `r` (for `r ≠ ½`): the second factor there equals
`2r − 1 ≠ 0`. -/
theorem realPair_order {r : ℝ} (hr : r ≠ 1 / 2) :
    analyticOrderAt (realPair r) (r : ℂ) = 1 := by
  have hfeq : realPair r = (fun s => s - (r : ℂ)) * (fun s => s - ((1 - r : ℝ) : ℂ)) := by
    funext s; simp only [realPair, Pi.mul_apply]
  have hlin_an : AnalyticAt ℂ (fun s : ℂ => s - (r : ℂ)) (r : ℂ) :=
    analyticAt_id.sub analyticAt_const
  have hg_an : AnalyticAt ℂ (fun s : ℂ => s - ((1 - r : ℝ) : ℂ)) (r : ℂ) :=
    analyticAt_id.sub analyticAt_const
  have hg0 : (r : ℂ) - ((1 - r : ℝ) : ℂ) ≠ 0 := by
    rw [show (r : ℂ) - ((1 - r : ℝ) : ℂ) = ((2 * r - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_ne_zero]
    intro h; apply hr; linarith
  have hord_lin : analyticOrderAt (fun s : ℂ => s - (r : ℂ)) (r : ℂ) = 1 :=
    analyticOrderAt_linGap_self _
  have hord_g : analyticOrderAt (fun s : ℂ => s - ((1 - r : ℝ) : ℂ)) (r : ℂ) = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hg0)
  rw [hfeq, analyticOrderAt_mul hlin_an hg_an, hord_lin, hord_g, add_zero]

/-! ### §3 The packing theorem: no local obstruction -/

/-- **No local obstruction to equivariant packing.**  Given a finite family of FE + Schwarz base
blocks `base j`, each with a simple zero at its own point `p j` and non-vanishing at every other
family point, the product of prescribed powers `∏ (base i)^(m i)` is again FE + Schwarz and has
vanishing order *exactly* `m j` at each point `p j`.  Every finite symmetric divisor supported on
such a configuration is realized by a single symmetric carrier. -/
theorem no_local_packing_obstruction {ι : Type*} (t : Finset ι) (p : ι → ℂ) (m : ι → ℕ)
    (base : ι → ℂ → ℂ)
    (hblock : ∀ j ∈ t, FESchwarz (base j))
    (hord : ∀ j ∈ t, analyticOrderAt (base j) (p j) = 1)
    (hother : ∀ j ∈ t, ∀ i ∈ t, i ≠ j → base i (p j) ≠ 0) :
    ∃ f : ℂ → ℂ, FESchwarz f ∧ ∀ j ∈ t, analyticOrderAt f (p j) = m j := by
  classical
  refine ⟨fun s => ∏ i ∈ t, (base i s) ^ (m i), ?_, ?_⟩
  · exact FESchwarz.finsetProd t (fun i s => (base i s) ^ (m i))
      (fun i hi => (hblock i hi).pow (m i))
  · intro j hj
    exact analyticOrderAt_prodPow_at t base m (p j) j hj
      (fun i hi => ((hblock i hi).1).analyticAt (p j)) (hord j hj) (hother j hj)

/-! ### §4 The concrete instantiation: arbitrary orders at arbitrary symmetric configurations -/

/-- **Every finite symmetric divisor is realizable.**  Given a finite configuration of generic
off-line off-real points `gen`, critical-line crease heights `crease`, and real off-line points `rl`,
together with the (blunt) hypotheses that every block is non-vanishing at every foreign point, there
is a single FE + Schwarz carrier `f` whose vanishing order is *exactly* the prescribed multiplicity at
each point of each family.  The equivariant cylinder-packing problem has no local obstruction: flat
symmetry constrains no symmetric divisor. -/
theorem symmetric_divisor_realizable
    (gen : Finset ℂ) (mgen : ℂ → ℕ)
    (crease : Finset ℝ) (mcr : ℝ → ℕ)
    (rl : Finset ℝ) (mrl : ℝ → ℕ)
    (hgen : ∀ ρ ∈ gen, ρ.re ≠ 1 / 2 ∧ ρ.im ≠ 0)
    (hcr : ∀ τ ∈ crease, τ ≠ 0)
    (hrl : ∀ r ∈ rl, r ≠ 1 / 2)
    (hA : ∀ ρ ∈ gen, ∀ ρ' ∈ gen, ρ' ≠ ρ → orbitQuartic ρ' ρ ≠ 0)
    (hB : ∀ ρ ∈ gen, ∀ τ ∈ crease, linePair τ ρ ≠ 0)
    (hC : ∀ ρ ∈ gen, ∀ r ∈ rl, realPair r ρ ≠ 0)
    (hD : ∀ τ ∈ crease, ∀ ρ ∈ gen,
      orbitQuartic ρ ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) ≠ 0)
    (hE : ∀ τ ∈ crease, ∀ τ' ∈ crease, τ' ≠ τ →
      linePair τ' ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) ≠ 0)
    (hF : ∀ τ ∈ crease, ∀ r ∈ rl,
      realPair r ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) ≠ 0)
    (hG : ∀ r ∈ rl, ∀ ρ ∈ gen, orbitQuartic ρ (r : ℂ) ≠ 0)
    (hH : ∀ r ∈ rl, ∀ τ ∈ crease, linePair τ (r : ℂ) ≠ 0)
    (hI : ∀ r ∈ rl, ∀ r' ∈ rl, r' ≠ r → realPair r' (r : ℂ) ≠ 0) :
    ∃ f : ℂ → ℂ, FESchwarz f ∧
      (∀ ρ ∈ gen, analyticOrderAt f ρ = mgen ρ) ∧
      (∀ τ ∈ crease, analyticOrderAt f ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) = mcr τ) ∧
      (∀ r ∈ rl, analyticOrderAt f (r : ℂ) = mrl r) := by
  classical
  set Fg : ℂ → ℂ := fun s => ∏ ρ ∈ gen, (orbitQuartic ρ s) ^ (mgen ρ) with hFg
  set Fc : ℂ → ℂ := fun s => ∏ τ ∈ crease, (linePair τ s) ^ (mcr τ) with hFc
  set Fr : ℂ → ℂ := fun s => ∏ r ∈ rl, (realPair r s) ^ (mrl r) with hFr
  have hFgFE : FESchwarz Fg :=
    FESchwarz.finsetProd gen (fun ρ s => (orbitQuartic ρ s) ^ (mgen ρ))
      (fun ρ _ => (fESchwarz_orbitQuartic ρ).pow (mgen ρ))
  have hFcFE : FESchwarz Fc :=
    FESchwarz.finsetProd crease (fun τ s => (linePair τ s) ^ (mcr τ))
      (fun τ _ => (fESchwarz_linePair τ).pow (mcr τ))
  have hFrFE : FESchwarz Fr :=
    FESchwarz.finsetProd rl (fun r s => (realPair r s) ^ (mrl r))
      (fun r _ => (fESchwarz_realPair r).pow (mrl r))
  refine ⟨fun s => Fg s * Fc s * Fr s, (hFgFE.mul hFcFE).mul hFrFE, ?_, ?_, ?_⟩
  · -- generic points: the orbit-quartic block is diagonal, the crease and real blocks vanish nowhere
    intro ρ₀ hρ₀
    have hAg : AnalyticAt ℂ Fg ρ₀ := hFgFE.1.analyticAt ρ₀
    have hAc : AnalyticAt ℂ Fc ρ₀ := hFcFE.1.analyticAt ρ₀
    have hAr : AnalyticAt ℂ Fr ρ₀ := hFrFE.1.analyticAt ρ₀
    have hAgc : AnalyticAt ℂ (fun s => Fg s * Fc s) ρ₀ := hAg.mul hAc
    have hsplit : (fun s => Fg s * Fc s * Fr s) = (fun s => Fg s * Fc s) * Fr := by
      funext s; simp only [Pi.mul_apply]
    have hsplit2 : (fun s => Fg s * Fc s) = Fg * Fc := by funext s; simp only [Pi.mul_apply]
    have hg_ord : analyticOrderAt Fg ρ₀ = (mgen ρ₀ : ℕ∞) := by
      rw [hFg]
      exact analyticOrderAt_prodPow_at gen orbitQuartic mgen ρ₀ ρ₀ hρ₀
        (fun ρ _ => (orbitQuartic_differentiable ρ).analyticAt ρ₀)
        (orbitQuartic_order_one (hgen ρ₀ hρ₀).1 (hgen ρ₀ hρ₀).2) (hA ρ₀ hρ₀)
    have hc_ord : analyticOrderAt Fc ρ₀ = 0 := by
      rw [hFc]; exact analyticOrderAt_prodPow_zero crease linePair mcr ρ₀ (hB ρ₀ hρ₀)
    have hr_ord : analyticOrderAt Fr ρ₀ = 0 := by
      rw [hFr]; exact analyticOrderAt_prodPow_zero rl realPair mrl ρ₀ (hC ρ₀ hρ₀)
    rw [hsplit, analyticOrderAt_mul hAgc hAr, hsplit2, analyticOrderAt_mul hAg hAc,
        hg_ord, hc_ord, hr_ord, add_zero, add_zero]
  · -- crease points: the crease block is diagonal, the orbit-quartic and real blocks vanish nowhere
    intro τ₀ hτ₀
    have hAg : AnalyticAt ℂ Fg ((1 / 2 : ℂ) + (τ₀ : ℂ) * Complex.I) := hFgFE.1.analyticAt _
    have hAc : AnalyticAt ℂ Fc ((1 / 2 : ℂ) + (τ₀ : ℂ) * Complex.I) := hFcFE.1.analyticAt _
    have hAr : AnalyticAt ℂ Fr ((1 / 2 : ℂ) + (τ₀ : ℂ) * Complex.I) := hFrFE.1.analyticAt _
    have hAgc : AnalyticAt ℂ (fun s => Fg s * Fc s) ((1 / 2 : ℂ) + (τ₀ : ℂ) * Complex.I) :=
      hAg.mul hAc
    have hsplit : (fun s => Fg s * Fc s * Fr s) = (fun s => Fg s * Fc s) * Fr := by
      funext s; simp only [Pi.mul_apply]
    have hsplit2 : (fun s => Fg s * Fc s) = Fg * Fc := by funext s; simp only [Pi.mul_apply]
    have hg_ord : analyticOrderAt Fg ((1 / 2 : ℂ) + (τ₀ : ℂ) * Complex.I) = 0 := by
      rw [hFg]; exact analyticOrderAt_prodPow_zero gen orbitQuartic mgen _ (hD τ₀ hτ₀)
    have hc_ord : analyticOrderAt Fc ((1 / 2 : ℂ) + (τ₀ : ℂ) * Complex.I) = (mcr τ₀ : ℕ∞) := by
      rw [hFc]
      exact analyticOrderAt_prodPow_at crease linePair mcr _ τ₀ hτ₀
        (fun τ _ => (fESchwarz_linePair τ).1.analyticAt _)
        (linePair_order (hcr τ₀ hτ₀)) (hE τ₀ hτ₀)
    have hr_ord : analyticOrderAt Fr ((1 / 2 : ℂ) + (τ₀ : ℂ) * Complex.I) = 0 := by
      rw [hFr]; exact analyticOrderAt_prodPow_zero rl realPair mrl _ (hF τ₀ hτ₀)
    rw [hsplit, analyticOrderAt_mul hAgc hAr, hsplit2, analyticOrderAt_mul hAg hAc,
        hg_ord, hc_ord, hr_ord, zero_add, add_zero]
  · -- real points: the real block is diagonal, the orbit-quartic and crease blocks vanish nowhere
    intro r₀ hr₀
    have hAg : AnalyticAt ℂ Fg (r₀ : ℂ) := hFgFE.1.analyticAt _
    have hAc : AnalyticAt ℂ Fc (r₀ : ℂ) := hFcFE.1.analyticAt _
    have hAr : AnalyticAt ℂ Fr (r₀ : ℂ) := hFrFE.1.analyticAt _
    have hAgc : AnalyticAt ℂ (fun s => Fg s * Fc s) (r₀ : ℂ) := hAg.mul hAc
    have hsplit : (fun s => Fg s * Fc s * Fr s) = (fun s => Fg s * Fc s) * Fr := by
      funext s; simp only [Pi.mul_apply]
    have hsplit2 : (fun s => Fg s * Fc s) = Fg * Fc := by funext s; simp only [Pi.mul_apply]
    have hg_ord : analyticOrderAt Fg (r₀ : ℂ) = 0 := by
      rw [hFg]; exact analyticOrderAt_prodPow_zero gen orbitQuartic mgen _ (hG r₀ hr₀)
    have hc_ord : analyticOrderAt Fc (r₀ : ℂ) = 0 := by
      rw [hFc]; exact analyticOrderAt_prodPow_zero crease linePair mcr _ (hH r₀ hr₀)
    have hr_ord : analyticOrderAt Fr (r₀ : ℂ) = (mrl r₀ : ℕ∞) := by
      rw [hFr]
      exact analyticOrderAt_prodPow_at rl realPair mrl _ r₀ hr₀
        (fun r _ => (fESchwarz_realPair r).1.analyticAt _)
        (realPair_order (hrl r₀ hr₀)) (hI r₀ hr₀)
    rw [hsplit, analyticOrderAt_mul hAgc hAr, hsplit2, analyticOrderAt_mul hAg hAc,
        hg_ord, hc_ord, hr_ord, zero_add, zero_add]

end RHTower
