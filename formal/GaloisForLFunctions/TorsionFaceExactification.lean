import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Pi

/-!
# The torsion face exactification engine

On suitable Taylor log-magnitude profiles, an integer-normalized algebraic differential equation
confines the dominant part of each coefficient identity to a fixed finite **face**: finitely many
multiplicity vectors `e : ι → ℕ` on a finite offset window `ι`, with entries bounded by the total
degree `D`, each carrying a complex weight (the limit of its normalized grouped integer weight).
A phase tail containing every finite root-of-unity word evaluates the face against every state
`s : ι → ℂ` with coordinates in `μ_m`, and the exponential bend inequality forces the weighted
character sum to vanish at every such state.

This file proves the two closing steps of such arguments.

* `face_weights_eq_zero`: if `∑ e ∈ F, ℓ e * ∏ i, s i ^ e i = 0` for every state `s` with
  `s i ^ m = 1`, and every multiplicity is at most `D < m`, then every weight `ℓ e` vanishes.
  Distinct multiplicity vectors bounded by `D` restrict to distinct characters of the finite
  state group, and averaging against one character isolates its weight (finite Fourier
  inversion on `(μ_m)^ι`).
* `polynomial_eq_zero_of_tendsto_zero`: a complex polynomial whose values along a strictly
  monotone sequence of naturals tend to `0` is the zero polynomial.  This converts an
  exponentially small bound on a fixed level polynomial, valid along an unbounded set of
  balanced indices, into identical vanishing of that level.
-/

open Finset

namespace GaloisForLFunctions

section Exactification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A primitive `m`-th root of unity raised to an integer power not divisible by `m` has
vanishing power sum over `range m`: the column sum of a nontrivial character of `ℤ/m`. -/
lemma sum_pow_zpow_eq_zero {m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {k : ℤ}
    (hk : ¬ (m : ℤ) ∣ k) : ∑ j ∈ range m, (ζ ^ k) ^ j = 0 := by
  have hne : ζ ^ k ≠ 1 := fun h1 => hk ((hζ.zpow_eq_one_iff_dvd k).mp h1)
  have hm1 : (ζ ^ k) ^ m = 1 := by
    have : (ζ ^ k) ^ (m : ℤ) = 1 := by
      rw [← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    simpa [zpow_natCast] using this
  rw [geom_sum_eq hne, hm1, sub_self, zero_div]

/-- **Torsion face exactification.**  Let `F` be a finite face of multiplicity vectors
`e : ι → ℕ` on a finite window `ι`, all entries at most `D`, with complex weights `ℓ`.  If the
weighted character sum `∑ e ∈ F, ℓ e * ∏ i, s i ^ e i` vanishes at every state `s : ι → ℂ` whose
coordinates are `m`-th roots of unity, where `D < m`, then every weight vanishes.  Multiplicity
vectors bounded by `D` are separated by the `m`-torsion character table, so simultaneous
vanishing on the full state group is Fourier inversion for the trivial function. -/
theorem face_weights_eq_zero {m D : ℕ} (hDm : D < m) (F : Finset (ι → ℕ))
    (hF : ∀ e ∈ F, ∀ i, e i ≤ D) (ℓ : (ι → ℕ) → ℂ)
    (hvanish : ∀ s : ι → ℂ, (∀ i, s i ^ m = 1) →
      ∑ e ∈ F, ℓ e * ∏ i, s i ^ e i = 0) :
    ∀ e ∈ F, ℓ e = 0 := by
  intro e₀ he₀
  have hm0 : m ≠ 0 := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hζdef
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm0
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0
  -- the vanishing hypothesis at the root-of-unity state attached to an exponent tuple
  have hx : ∀ x : ι → ℕ, ∑ e ∈ F, ℓ e * ∏ i, ζ ^ ((e i : ℤ) * (x i : ℤ)) = 0 := by
    intro x
    have h1 : ∀ i : ι, (ζ ^ x i) ^ m = 1 := by
      intro i
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have h2 := hvanish (fun i => ζ ^ x i) h1
    calc ∑ e ∈ F, ℓ e * ∏ i, ζ ^ ((e i : ℤ) * (x i : ℤ))
        = ∑ e ∈ F, ℓ e * ∏ i, (ζ ^ x i) ^ e i := by
          refine Finset.sum_congr rfl fun e _ => ?_
          congr 1
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← pow_mul, ← zpow_natCast ζ (x i * e i)]
          congr 1
          push_cast
          ring
      _ = 0 := h2
  -- off-diagonal characters have vanishing state sums
  have key : ∀ e ∈ F, e ≠ e₀ →
      ∏ i, (∑ j ∈ range m, (ζ ^ ((e i : ℤ) - (e₀ i : ℤ))) ^ j) = 0 := by
    intro e heF hne
    obtain ⟨i₀, hi₀⟩ : ∃ i, e i ≠ e₀ i := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) (sum_pow_zpow_eq_zero hζ ?_)
    intro hdvd
    have habs : |(e i₀ : ℤ) - (e₀ i₀ : ℤ)| < (m : ℤ) := by
      rw [abs_lt]
      have h1 := hF e heF i₀
      have h2 := hF e₀ he₀ i₀
      omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    omega
  -- the diagonal character contributes the full state count
  have diag : ∏ i : ι, (∑ j ∈ range m, (ζ ^ ((e₀ i : ℤ) - (e₀ i : ℤ))) ^ j)
      = (m : ℂ) ^ Fintype.card ι := by
    have hone : ∀ i : ι, (∑ j ∈ range m, (ζ ^ ((e₀ i : ℤ) - (e₀ i : ℤ))) ^ j) = (m : ℂ) := by
      intro i
      simp
    rw [Finset.prod_congr rfl fun i _ => hone i, Finset.prod_const, Finset.card_univ]
  -- Fourier-average the vanishing identities against the character of `e₀`
  have master :
      ∑ e ∈ F, ℓ e * ∏ i, (∑ j ∈ range m, (ζ ^ ((e i : ℤ) - (e₀ i : ℤ))) ^ j) = 0 := by
    have hrw : ∀ e ∈ F,
        ℓ e * ∏ i, (∑ j ∈ range m, (ζ ^ ((e i : ℤ) - (e₀ i : ℤ))) ^ j)
          = ∑ x ∈ Fintype.piFinset (fun _ : ι => range m),
              (∏ i, ζ ^ (-((e₀ i : ℤ)) * (x i : ℤ))) *
                (ℓ e * ∏ i, ζ ^ ((e i : ℤ) * (x i : ℤ))) := by
      intro e _
      rw [Finset.prod_univ_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hsplit : ∀ i : ι, (ζ ^ ((e i : ℤ) - (e₀ i : ℤ))) ^ (x i)
          = ζ ^ (-((e₀ i : ℤ)) * (x i : ℤ)) * ζ ^ ((e i : ℤ) * (x i : ℤ)) := by
        intro i
        rw [← zpow_natCast (ζ ^ ((e i : ℤ) - (e₀ i : ℤ))) (x i), ← zpow_mul,
          ← zpow_add₀ hζ0]
        congr 1
        ring
      rw [Finset.prod_congr rfl fun i _ => hsplit i, Finset.prod_mul_distrib]
      ring
    calc ∑ e ∈ F, ℓ e * ∏ i, (∑ j ∈ range m, (ζ ^ ((e i : ℤ) - (e₀ i : ℤ))) ^ j)
        = ∑ e ∈ F, ∑ x ∈ Fintype.piFinset (fun _ : ι => range m),
            (∏ i, ζ ^ (-((e₀ i : ℤ)) * (x i : ℤ))) *
              (ℓ e * ∏ i, ζ ^ ((e i : ℤ) * (x i : ℤ))) :=
          Finset.sum_congr rfl hrw
      _ = ∑ x ∈ Fintype.piFinset (fun _ : ι => range m),
            (∏ i, ζ ^ (-((e₀ i : ℤ)) * (x i : ℤ))) *
              ∑ e ∈ F, ℓ e * ∏ i, ζ ^ ((e i : ℤ) * (x i : ℤ)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
      _ = 0 := Finset.sum_eq_zero fun x _ => by rw [hx x, mul_zero]
  -- isolate the diagonal and cancel the nonzero state count
  have final : ℓ e₀ * (m : ℂ) ^ Fintype.card ι = 0 := by
    have hsingle : ∑ e ∈ F, ℓ e * ∏ i, (∑ j ∈ range m, (ζ ^ ((e i : ℤ) - (e₀ i : ℤ))) ^ j)
        = ℓ e₀ * ∏ i, (∑ j ∈ range m, (ζ ^ ((e₀ i : ℤ) - (e₀ i : ℤ))) ^ j) := by
      refine Finset.sum_eq_single e₀ (fun e heF hne => ?_) (fun h => absurd he₀ h)
      rw [key e heF hne, mul_zero]
    rw [hsingle, diag] at master
    exact master
  have hmne : ((m : ℂ)) ^ Fintype.card ι ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast hm0
  exact (mul_eq_zero.mp final).resolve_right hmne

end Exactification

section LevelVanishing

open Filter

/-- A complex polynomial whose values along a strictly monotone sequence of naturals tend to zero
is the zero polynomial: a nonconstant polynomial has `‖P(z)‖ → ∞` along any sequence with
`‖z‖ → ∞`, and a constant polynomial equals its limit.  This is the level-vanishing step: an
exponentially small bound on a fixed level polynomial along an unbounded set of integers forces
the level to vanish identically. -/
theorem polynomial_eq_zero_of_tendsto_zero (P : Polynomial ℂ) (u : ℕ → ℕ) (hu : StrictMono u)
    (h : Tendsto (fun k => P.eval ((u k : ℕ) : ℂ)) atTop (nhds 0)) : P = 0 := by
  rcases le_or_gt P.degree 0 with hdeg | hdeg
  · have hC := Polynomial.eq_C_of_degree_le_zero hdeg
    have hval : Tendsto (fun _ : ℕ => P.coeff 0) atTop (nhds 0) := by
      have heq : (fun k => P.eval ((u k : ℕ) : ℂ)) = fun _ => P.coeff 0 := by
        funext k
        conv_lhs => rw [hC]
        exact Polynomial.eval_C
      rwa [heq] at h
    have hc0 : P.coeff 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hval
    rw [hC, hc0]
    exact Polynomial.C_0
  · exfalso
    have hz : Tendsto (fun k => ‖((u k : ℕ) : ℂ)‖) atTop atTop := by
      have h1 : Tendsto (fun k => ((u k : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hu.tendsto_atTop
      simpa [Complex.norm_natCast] using h1
    have hblow : Tendsto (fun k => ‖P.eval ((u k : ℕ) : ℂ)‖) atTop atTop :=
      P.tendsto_norm_atTop hdeg hz
    have h0 : Tendsto (fun k => ‖P.eval ((u k : ℕ) : ℂ)‖) atTop (nhds 0) := by
      simpa using h.norm
    obtain ⟨k, hk1, hk2⟩ := ((hblow.eventually_ge_atTop 1).and
      (h0.eventually (gt_mem_nhds one_pos))).exists
    linarith

end LevelVanishing

end GaloisForLFunctions
