import GaloisForLFunctions.MultiplicativePositivityGeometry.ZetaBoundaryDivisor
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Families over a finite abelian group: the two-torsion exception

Let `G` be a finite abelian group and `(Z_g)_{g ∈ G}` a family of Euler products whose
log-coefficients at a frequency `λ` are `w · ψ(g)` for a character `ψ` of `G` and a weight `w ≥ 0`.
The model is the Dirichlet family mod `q`: `G` is the character group, `g = χ`, and the
log-coefficient of `L(s, χ)` at `log n` is `Λ(n) χ(n)`, where `χ ↦ χ(n)` is a character of `G`. The
joint trace `(g, u) ↦ Σ_i w_i Re(ψ_i(g) e^{iλ_i u})` (`jointTrace`) is a positive combination of
characters of `G × ℝ`, hence positive definite there (`isEvenPosDef_jointTrace`). So is the joint
boundary divisor `𝒟(g, u)`: pole order minus zero order of `Z_g` at `1 + iu`
(`IsJointBoundaryDivisor.isEvenPosDef`).

* **Joint forcing law** (`joint_forcing_law`). If `𝒟` is integer valued, `𝒟(0, 0) = 1` and
  `𝒟 ≤ 0` away from `(0, 0)`, then either `𝒟 = δ_{(0,0)}`, or `𝒟 = δ_{(0,0)} − δ_{(h,0)}` for a
  single `h ≠ 0` with `2h = 0`. A boundary zero can only sit at the pole `s = 1`, on one member of
  order two.
* **The exception occurs** (`exceptional_isJointBoundaryDivisor`). For every `h ≠ 0` with `2h = 0`
  the weights `Λ(n) n^{−1−x} (1 − ψ(h))/|G|` on the frequencies `(ψ, log n)` have joint divisor
  `δ_{(0,0)} − δ_{(h,0)}`: the family `Z_g` has a simple pole at `g = 0` and a simple zero at
  `s = 1` on `g = h`. For `G = ℤ/2` it is the pair `(ζ, 1/ζ)`.

For Dirichlet characters, boundary positivity proves `L(1 + iu, χ) ≠ 0` for `u ≠ 0` and
`L(1, χ) ≠ 0` for `χ² ≠ 1`, and allows at most one real `χ` with `L(1, χ) = 0`. It cannot exclude
that one: the exceptional configuration is positive definite and realized. Excluding it requires
information off the boundary, on the real axis inside the strip (the positivity of `ζ L(·, χ)` on
`(−2, 1)`). The exceptional real character is the two-torsion of the family group.
-/

open Finset Filter Topology Complex

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

section Family

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- On a finite group, `conj ψ(a) = ψ(−a)`. -/
theorem conj_addChar_apply (ψ : AddChar G ℂ) (a : G) : (starRingEnd ℂ) (ψ a) = ψ (-a) := by
  have hn : ψ a ^ Fintype.card G = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  have hnorm : ‖ψ a‖ = 1 := norm_eq_one_of_pow_eq_one hn Fintype.card_ne_zero
  have hsq : Complex.normSq (ψ a) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm, one_pow]
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, hsq]
  simp

/-- The joint phase `ψ(g) e^{iλu}` of a point `(g, u)`. -/
noncomputable def jointPhase (ψ : AddChar G ℂ) (lam : ℝ) (p : G × ℝ) : ℂ :=
  ψ p.1 * Complex.exp (((lam * p.2 : ℝ) : ℂ) * I)

/-- One joint mode `Re(ψ(g) e^{iλu})`. -/
noncomputable def jointMode (ψ : AddChar G ℂ) (lam : ℝ) (p : G × ℝ) : ℝ :=
  (jointPhase ψ lam p).re

theorem jointPhase_sub (ψ : AddChar G ℂ) (lam : ℝ) (p q : G × ℝ) :
    jointPhase ψ lam (p - q) = jointPhase ψ lam p * (starRingEnd ℂ) (jointPhase ψ lam q) := by
  unfold jointPhase
  rw [map_mul, conj_addChar_apply, ← Complex.exp_conj, Prod.fst_sub, Prod.snd_sub,
    sub_eq_add_neg p.1, AddChar.map_add_eq_mul]
  have h : (starRingEnd ℂ) (((lam * q.2 : ℝ) : ℂ) * I) = -(((lam * q.2 : ℝ) : ℂ) * I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [h, show (((lam * (p.2 - q.2) : ℝ) : ℂ) * I) =
      ((lam * p.2 : ℝ) : ℂ) * I + -(((lam * q.2 : ℝ) : ℂ) * I) by push_cast; ring,
    Complex.exp_add]
  ring

theorem norm_addChar_apply (ψ : AddChar G ℂ) (a : G) : ‖ψ a‖ = 1 := by
  have hn : ψ a ^ Fintype.card G = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  exact norm_eq_one_of_pow_eq_one hn Fintype.card_ne_zero

theorem norm_jointPhase (ψ : AddChar G ℂ) (lam : ℝ) (p : G × ℝ) : ‖jointPhase ψ lam p‖ = 1 := by
  rw [jointPhase, norm_mul, norm_addChar_apply, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem abs_jointMode_le (ψ : AddChar G ℂ) (lam : ℝ) (p : G × ℝ) : |jointMode ψ lam p| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (norm_jointPhase ψ lam p).le

/-- Gram forms of `Re(z_j conj z_k)` are squared norms. -/
theorem gram_re_mul_conj {n : ℕ} (z : Fin n → ℂ) (c : Fin n → ℝ) :
    ∑ j, ∑ k, c j * c k * (z j * (starRingEnd ℂ) (z k)).re = ‖∑ j, (c j : ℂ) * z j‖ ^ 2 := by
  have hw : (∑ j, (c j : ℂ) * z j) * (starRingEnd ℂ) (∑ j, (c j : ℂ) * z j) =
      ∑ j, ∑ k, ((c j * c k : ℝ) : ℂ) * (z j * (starRingEnd ℂ) (z k)) := by
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have hn : ‖∑ j, (c j : ℂ) * z j‖ ^ 2 =
      ((∑ j, (c j : ℂ) * z j) * (starRingEnd ℂ) (∑ j, (c j : ℂ) * z j)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hn, hw, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun k _ => (Complex.re_ofReal_mul _ _).symm

/-- A joint mode is a real character of `G × ℝ`, hence even positive definite. -/
theorem jointMode_isEvenPosDef (ψ : AddChar G ℂ) (lam : ℝ) : IsEvenPosDef (jointMode ψ lam) where
  even p := by
    have h := jointPhase_sub ψ lam 0 p
    have h0 : jointPhase ψ lam 0 = 1 := by simp [jointPhase]
    rw [zero_sub, h0, one_mul] at h
    rw [jointMode, h, Complex.conj_re, jointMode]
  posDef n x c := by
    have h := gram_re_mul_conj (fun j => jointPhase ψ lam (x j)) c
    simp only [jointMode, jointPhase_sub]
    rw [h]
    positivity

/-- The joint trace `(g, u) ↦ Σ_i w_i Re(ψ_i(g) e^{iλ_i u})`. -/
noncomputable def jointTrace {ι : Type*} (w : ι → ℝ) (ψ : ι → AddChar G ℂ) (lam : ι → ℝ)
    (p : G × ℝ) : ℝ :=
  ∑' i, w i * jointMode (ψ i) (lam i) p

theorem summable_jointTrace_terms {ι : Type*} {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hs : Summable w)
    (ψ : ι → AddChar G ℂ) (lam : ι → ℝ) (p : G × ℝ) :
    Summable fun i => w i * jointMode (ψ i) (lam i) p :=
  Summable.of_norm_bounded hs fun i => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i)]
    exact mul_le_of_le_one_right (hw i) (abs_jointMode_le _ _ _)

/-- **Joint positivity.** Nonnegative weights give an even positive-definite joint trace on
`G × ℝ`. -/
theorem isEvenPosDef_jointTrace {ι : Type*} {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hs : Summable w)
    (ψ : ι → AddChar G ℂ) (lam : ι → ℝ) : IsEvenPosDef (jointTrace w ψ lam) where
  even p := by
    unfold jointTrace
    exact tsum_congr fun i => by rw [(jointMode_isEvenPosDef (ψ i) (lam i)).even]
  posDef n x c := by
    have hall : HasSum
        (fun i => ∑ j, ∑ k, c j * c k * (w i * jointMode (ψ i) (lam i) (x j - x k)))
        (∑ j, ∑ k, c j * c k * jointTrace w ψ lam (x j - x k)) :=
      hasSum_sum fun j _ => hasSum_sum fun k _ =>
        ((summable_jointTrace_terms hw hs ψ lam (x j - x k)).hasSum).mul_left _
    refine hall.nonneg fun i => ?_
    have h : ∑ j, ∑ k, c j * c k * (w i * jointMode (ψ i) (lam i) (x j - x k)) =
        w i * ∑ j, ∑ k, c j * c k * jointMode (ψ i) (lam i) (x j - x k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h]
    exact mul_nonneg (hw i) ((jointMode_isEvenPosDef (ψ i) (lam i)).posDef n x c)

/-- A joint boundary datum: damped nonnegative weights on characters of `G` and real frequencies
whose normalized joint traces converge to the joint divisor `𝒟`. -/
structure IsJointBoundaryDivisor {ι : Type*} (ψ : ι → AddChar G ℂ) (lam : ι → ℝ)
    (w : ℝ → ι → ℝ) (𝒟 : G × ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 < x → ∀ i, 0 ≤ w x i
  summable : ∀ x, 0 < x → Summable (w x)
  tendsto : ∀ p, Tendsto (fun x => x * jointTrace (w x) ψ lam p) (𝓝[>] 0) (𝓝 (𝒟 p))

/-- **Joint boundary positivity.** The joint divisor is even positive definite on `G × ℝ`. -/
theorem IsJointBoundaryDivisor.isEvenPosDef {ι : Type*} {ψ : ι → AddChar G ℂ} {lam : ι → ℝ}
    {w : ℝ → ι → ℝ} {𝒟 : G × ℝ → ℝ} (h : IsJointBoundaryDivisor ψ lam w 𝒟) :
    IsEvenPosDef 𝒟 :=
  isEvenPosDef_of_tendsto (l := 𝓝[>] (0 : ℝ)) (F := fun x p => x * jointTrace (w x) ψ lam p)
    (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (isEvenPosDef_jointTrace (h.nonneg x hx) (h.summable x hx) ψ lam).smul (le_of_lt hx))
    h.tendsto

end Family

/-! ### The joint forcing law -/

section Forcing

variable {Γ : Type*} [AddCommGroup Γ]

open Classical in
/-- **Joint forcing law.** An integer-valued even positive-definite `𝒟` on `G × ℝ` with
`𝒟(0) = 1` and `𝒟 ≤ 0` off the origin is either `δ₀`, or `δ₀ − δ_{(h,0)}` for a single
`h ≠ 0` with `2h = 0`. -/
theorem joint_forcing_law {G : Type*} [AddCommGroup G] {𝒟 : G × ℝ → ℝ} (hD : IsEvenPosDef 𝒟)
    (h0 : 𝒟 0 = 1) (hint : ∀ p, ∃ n : ℤ, 𝒟 p = n) (hnp : ∀ p, p ≠ 0 → 𝒟 p ≤ 0) :
    (∀ p, 𝒟 p = if p = 0 then 1 else 0) ∨
      ∃ h : G, h ≠ 0 ∧ h + h = 0 ∧
        ∀ p, 𝒟 p = (if p = 0 then 1 else 0) - (if p = (h, 0) then 1 else 0) := by
  classical
  by_cases hex : ∃ q, 𝒟 q = -1
  · right
    obtain ⟨q, hq⟩ := hex
    have hq2 : q + q = 0 := by
      by_contra hne
      have := hnp _ hne
      rw [intValued_double hD h0 hint hq] at this
      linarith
    have hq0 : q ≠ 0 := fun h => by rw [h, h0] at hq; linarith
    have hqu : q.2 = 0 := by
      have := congrArg Prod.snd hq2
      simp only [Prod.snd_add, Prod.snd_zero] at this
      linarith
    have hqh : q = (q.1, 0) := Prod.ext rfl hqu
    have hh0 : q.1 ≠ 0 := fun h => hq0 (by rw [hqh, h]; rfl)
    refine ⟨q.1, hh0, by simpa using congrArg Prod.fst hq2, fun p => ?_⟩
    rw [← hqh]
    -- `q` is the only point with value `−1`.
    have huniq : ∀ p, 𝒟 p = -1 → p = q := by
      intro p hp
      have hmul := intValued_mul hD h0 hint (h := q) (by rw [hq]; norm_num) p
      rw [hq, hp] at hmul
      have hpq : q + p = 0 := by
        by_contra hne
        have := hnp _ hne
        linarith
      calc p = -q := eq_neg_of_add_eq_zero_right hpq
        _ = q := neg_eq_of_add_eq_zero_right hq2
    rcases intValued_values hD h0 hint p with h1 | h1 | h1
    · have := huniq p h1
      subst this
      rw [if_neg hq0, if_pos rfl, h1]
      ring
    · rw [h1]
      split_ifs with ha hb hb
      · rw [ha, h0] at h1; norm_num at h1
      · rw [ha, h0] at h1; norm_num at h1
      · rw [hb, hq] at h1; norm_num at h1
      · ring
    · have hp0 : p = 0 := by
        by_contra hne
        have := hnp p hne
        linarith
      subst hp0
      rw [if_pos rfl, if_neg (Ne.symm hq0), h1]
      ring
  · left
    push Not at hex
    intro p
    split_ifs with hp
    · rw [hp, h0]
    · rcases intValued_values hD h0 hint p with h1 | h1 | h1
      · exact absurd h1 (hex p)
      · exact h1
      · have := hnp p hp
        linarith

end Forcing

/-! ### The exceptional family -/

section Exception

universe u

variable {G : Type u} [AddCommGroup G] [Fintype G]

/-- A character takes a real value `± 1` at a point of order two. -/
theorem addChar_apply_im_eq_zero {h : G} (hh : h + h = 0) (ψ : AddChar G ℂ) : (ψ h).im = 0 := by
  have hneg : -h = h := neg_eq_of_add_eq_zero_right hh
  have hc := conj_addChar_apply ψ h
  rw [hneg] at hc
  exact Complex.conj_eq_iff_im.mp hc

/-- Character orthogonality: `Σ_ψ (1 − ψ(h)) Re(ψ(g) e^{iθ}) = |G| ([g = 0] − [g = h]) cos θ`. -/
theorem sum_exceptional_mode [DecidableEq G] {h : G} (hh : h + h = 0) (g : G) (θ : ℝ) :
    ∑ ψ : AddChar G ℂ, (1 - (ψ h).re) * (ψ g * Complex.exp ((θ : ℂ) * I)).re =
      Fintype.card G * ((if g = 0 then 1 else 0) - (if g = h then 1 else 0)) * Real.cos θ := by
  have hneg : -h = h := neg_eq_of_add_eq_zero_right hh
  have hterm : ∀ ψ : AddChar G ℂ, (1 - (ψ h).re) * (ψ g * Complex.exp ((θ : ℂ) * I)).re =
      ((ψ g - ψ (g + h)) * Complex.exp ((θ : ℂ) * I)).re := by
    intro ψ
    have hre : (ψ h : ℂ) = ((ψ h).re : ℂ) := by
      apply Complex.ext <;> simp [addChar_apply_im_eq_zero hh]
    rw [← Complex.re_ofReal_mul, AddChar.map_add_eq_mul]
    congr 1
    conv_rhs => rw [hre]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun ψ _ => hterm ψ, ← Complex.re_sum, ← Finset.sum_mul,
    Finset.sum_sub_distrib, AddChar.sum_apply_eq_ite, AddChar.sum_apply_eq_ite]
  have hgh : (g + h = 0) ↔ (g = h) := by
    constructor
    · intro e; rw [← hneg]; exact eq_neg_of_add_eq_zero_left e
    · intro e; rw [e, hh]
  simp only [hgh]
  split_ifs <;> simp [Complex.exp_ofReal_mul_I_re]

/-- The exceptional weights `Λ(n) n^{−1−x} (1 − ψ(h))/|G|` on the frequencies `(log n, ψ)`. -/
noncomputable def exceptionalWeight (h : G) (x : ℝ) (p : ℕ × AddChar G ℂ) : ℝ :=
  zetaBoundaryWeight x p.1 * ((1 - (p.2 h).re) / Fintype.card G)

/-- The exceptional joint divisor `δ_{(0,0)} − δ_{(h,0)}`. -/
noncomputable def exceptionalDivisor [DecidableEq G] (h : G) (p : G × ℝ) : ℝ :=
  (if p = 0 then 1 else 0) - (if p = (h, 0) then 1 else 0)

theorem exceptionalWeight_nonneg (h : G) (x : ℝ) (p : ℕ × AddChar G ℂ) :
    0 ≤ exceptionalWeight h x p := by
  unfold exceptionalWeight
  refine mul_nonneg (zetaBoundaryWeight_nonneg x p.1) (div_nonneg ?_ (Nat.cast_nonneg _))
  have := (Complex.re_le_norm (p.2 h)).trans (norm_addChar_apply p.2 h).le
  linarith

theorem exceptionalWeight_le (h : G) (x : ℝ) (p : ℕ × AddChar G ℂ) :
    exceptionalWeight h x p ≤ 2 * zetaBoundaryWeight x p.1 := by
  unfold exceptionalWeight
  have hG : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos
  have h1 : (1 - (p.2 h).re) / Fintype.card G ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    have := neg_abs_le (p.2 h).re
    have := (Complex.abs_re_le_norm (p.2 h)).trans (norm_addChar_apply p.2 h).le
    nlinarith
  rw [mul_comm 2]
  exact mul_le_mul_of_nonneg_left h1 (zetaBoundaryWeight_nonneg x p.1)

theorem summable_exceptionalWeight (h : G) {x : ℝ} (hx : 0 < x) :
    Summable (exceptionalWeight h x) := by
  refine Summable.of_nonneg_of_le (exceptionalWeight_nonneg h x) (exceptionalWeight_le h x) ?_
  refine (summable_prod_of_nonneg fun p => by
    simpa using mul_nonneg zero_le_two (zetaBoundaryWeight_nonneg x p.1)).mpr
    ⟨fun _ => Summable.of_finite, ?_⟩
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ((summable_zetaBoundaryWeight hx).mul_left 2).mul_left _

/-- The exceptional joint trace is `([g = 0] − [g = h])` times the trace of `ζ`. -/
theorem jointTrace_exceptional [DecidableEq G] (h : G) (hh : h + h = 0) {x : ℝ} (hx : 0 < x) (p : G × ℝ) :
    jointTrace (exceptionalWeight h x) Prod.snd (fun q => logFrequency q.1) p =
      ((if p.1 = 0 then 1 else 0) - (if p.1 = h then 1 else 0)) *
        cosineTrace (zetaBoundaryWeight x) logFrequency p.2 := by
  have hs := summable_jointTrace_terms (exceptionalWeight_nonneg h x)
    (summable_exceptionalWeight h hx) Prod.snd (fun q => logFrequency q.1) p
  unfold jointTrace cosineTrace
  rw [hs.tsum_prod, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [tsum_fintype]
  have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have key := sum_exceptional_mode hh p.1 (logFrequency n * p.2)
  simp only [exceptionalWeight, jointMode, jointPhase]
  calc ∑ ψ : AddChar G ℂ, zetaBoundaryWeight x n * ((1 - (ψ h).re) / Fintype.card G) *
        (ψ p.1 * Complex.exp (((logFrequency n * p.2 : ℝ) : ℂ) * I)).re
      = zetaBoundaryWeight x n / Fintype.card G * ∑ ψ : AddChar G ℂ, (1 - (ψ h).re) *
          (ψ p.1 * Complex.exp (((logFrequency n * p.2 : ℝ) : ℂ) * I)).re := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ψ _ => by ring
    _ = _ := by
        rw [key]
        field_simp

/-- **The exception occurs.** For `h ≠ 0` with `2h = 0`, the exceptional weights have joint
divisor `δ_{(0,0)} − δ_{(h,0)}`: a family with a simple pole at `g = 0` and a simple zero at
`s = 1` on the member `g = h`. -/
theorem exceptional_isJointBoundaryDivisor [DecidableEq G] (h : G) (hh : h + h = 0) :
    IsJointBoundaryDivisor Prod.snd (fun q : ℕ × AddChar G ℂ => logFrequency q.1)
      (exceptionalWeight h) (exceptionalDivisor h) where
  nonneg x _ p := exceptionalWeight_nonneg h x p
  summable x hx := summable_exceptionalWeight h hx
  tendsto p := by
    have hlim := (zeta_isBoundaryDivisor.tendsto p.2).const_mul
      ((if p.1 = 0 then 1 else 0) - (if p.1 = h then 1 else 0) : ℝ)
    have heq : ((if p.1 = 0 then 1 else 0) - (if p.1 = h then 1 else 0) : ℝ) *
        zetaBoundaryDivisor p.2 = exceptionalDivisor h p := by
      rw [zetaBoundaryDivisor_eq, exceptionalDivisor]
      obtain ⟨g, u⟩ := p
      by_cases hu : u = 0
      · subst hu
        by_cases hg : g = 0
        · subst hg
          simp [Prod.ext_iff]
        · simp [hg, Prod.ext_iff]
      · simp [hu, Prod.ext_iff]
    rw [heq] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [jointTrace_exceptional h hh (Set.mem_Ioi.mp hx)]
    ring

/-- Orthogonality: `Σ_ψ Re(ψ(g) e^{iθ}) = |G| [g = 0] cos θ`. -/
theorem sum_regular_mode [DecidableEq G] (g : G) (θ : ℝ) :
    ∑ ψ : AddChar G ℂ, (ψ g * Complex.exp ((θ : ℂ) * I)).re =
      Fintype.card G * (if g = 0 then 1 else 0) * Real.cos θ := by
  rw [← Complex.re_sum, ← Finset.sum_mul, AddChar.sum_apply_eq_ite]
  split_ifs <;> simp [Complex.exp_ofReal_mul_I_re]

/-- The regular weights `Λ(n) n^{−1−x}/|G|` on the frequencies `(log n, ψ)`. -/
noncomputable def regularWeight (x : ℝ) (p : ℕ × AddChar G ℂ) : ℝ :=
  zetaBoundaryWeight x p.1 / Fintype.card G

theorem regularWeight_nonneg (x : ℝ) (p : ℕ × AddChar G ℂ) : 0 ≤ regularWeight x p :=
  div_nonneg (zetaBoundaryWeight_nonneg x p.1) (Nat.cast_nonneg _)

theorem summable_regularWeight {x : ℝ} (hx : 0 < x) :
    Summable (regularWeight (G := G) x) := by
  refine (summable_prod_of_nonneg fun p => regularWeight_nonneg x p).mpr
    ⟨fun _ => Summable.of_finite, ?_⟩
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, regularWeight]
  exact ((summable_zetaBoundaryWeight hx).div_const _).mul_left _

/-- The regular joint trace is `[g = 0]` times the trace of `ζ`. -/
theorem jointTrace_regular [DecidableEq G] {x : ℝ} (hx : 0 < x) (p : G × ℝ) :
    jointTrace (regularWeight x) Prod.snd (fun q => logFrequency q.1) p =
      (if p.1 = 0 then 1 else 0) * cosineTrace (zetaBoundaryWeight x) logFrequency p.2 := by
  have hs := summable_jointTrace_terms (regularWeight_nonneg x)
    (summable_regularWeight (G := G) hx) Prod.snd (fun q => logFrequency q.1) p
  unfold jointTrace cosineTrace
  rw [hs.tsum_prod, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [tsum_fintype]
  have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have key := sum_regular_mode p.1 (logFrequency n * p.2)
  simp only [regularWeight, jointMode, jointPhase]
  rw [show ∑ ψ : AddChar G ℂ, zetaBoundaryWeight x n / Fintype.card G *
      (ψ p.1 * Complex.exp (((logFrequency n * p.2 : ℝ) : ℂ) * I)).re =
      zetaBoundaryWeight x n / Fintype.card G * ∑ ψ : AddChar G ℂ,
        (ψ p.1 * Complex.exp (((logFrequency n * p.2 : ℝ) : ℂ) * I)).re by
      rw [Finset.mul_sum], key]
  field_simp

/-- **The regular family.** The weights `Λ(n) n^{−1−x}/|G|` have joint divisor `δ_{(0,0)}`. -/
theorem regular_isJointBoundaryDivisor [DecidableEq G] :
    IsJointBoundaryDivisor Prod.snd (fun q : ℕ × AddChar G ℂ => logFrequency q.1)
      regularWeight fun p : G × ℝ => if p = 0 then 1 else 0 where
  nonneg x _ p := regularWeight_nonneg x p
  summable x hx := summable_regularWeight hx
  tendsto p := by
    have hlim := (zeta_isBoundaryDivisor.tendsto p.2).const_mul
      ((if p.1 = 0 then 1 else 0) : ℝ)
    have heq : ((if p.1 = 0 then 1 else 0) : ℝ) * zetaBoundaryDivisor p.2 =
        if p = 0 then 1 else 0 := by
      rw [zetaBoundaryDivisor_eq]
      obtain ⟨g, u⟩ := p
      by_cases hu : u = 0 <;> by_cases hg : g = 0 <;> simp [hu, hg, Prod.ext_iff]
    rw [heq] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [jointTrace_regular (Set.mem_Ioi.mp hx)]
    ring

/-- **What boundary positivity permits for a finite family.** For a finite abelian group `G`, an
integer-valued `𝒟` on `G × ℝ` with `𝒟(0) = 1` and `𝒟 ≤ 0` off the origin is a joint boundary
divisor iff it is `δ₀` or `δ₀ − δ_{(h,0)}` for some `h ≠ 0` with `2h = 0`. -/
theorem joint_boundary_classification [DecidableEq G] {𝒟 : G × ℝ → ℝ}
    (hint : ∀ p, ∃ n : ℤ, 𝒟 p = n) (h0 : 𝒟 0 = 1) (hnp : ∀ p, p ≠ 0 → 𝒟 p ≤ 0) :
    (∃ (ι : Type u) (ψ : ι → AddChar G ℂ) (lam : ι → ℝ) (w : ℝ → ι → ℝ),
        IsJointBoundaryDivisor ψ lam w 𝒟) ↔
      (𝒟 = fun p => if p = 0 then 1 else 0) ∨
        ∃ h : G, h ≠ 0 ∧ h + h = 0 ∧ 𝒟 = exceptionalDivisor h := by
  constructor
  · rintro ⟨ι, ψ, lam, w, hw⟩
    rcases joint_forcing_law hw.isEvenPosDef h0 hint hnp with hδ | ⟨h, hh0, hh, hδ⟩
    · left
      funext p
      rw [hδ p]
      congr 1
    · right
      refine ⟨h, hh0, hh, funext fun p => ?_⟩
      rw [hδ p, exceptionalDivisor]
      congr 1 <;> congr 1
  · rintro (rfl | ⟨h, -, hh, rfl⟩)
    · exact ⟨_, _, _, _, regular_isJointBoundaryDivisor⟩
    · exact ⟨_, _, _, _, exceptional_isJointBoundaryDivisor h hh⟩

end Exception

end GaloisForLFunctions.MultiplicativePositivityGeometry
