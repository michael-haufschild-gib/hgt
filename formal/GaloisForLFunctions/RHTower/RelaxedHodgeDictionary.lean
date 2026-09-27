import GaloisForLFunctions.RHTower.EdgeConcentratedWeilTests

/-!
# The relaxed Hodge index: error exponent against zero depth

The **relaxed Hodge index** at level `a` with exponent `θ` (`RelaxedHodgeIndexAtLevel Z θ a`) asks
that `Re W(f, f) ≥ -e^{θa} ∫|f|²` for every polar-constrained `C²` test supported in `[-a, a]`.
`θ = -∞` is the Hodge index, and the prime-transport norm gives `θ = 1` unconditionally.

`exists_relaxed_violation` shows that a zero of depth `δ` breaks the relaxed index as soon as
`2δ` beats `θ` by the losses of the construction.  The test is the edge test of
`EdgeConcentratedWeilTests`, centred at a zero `ρs` that no zero within ordinate `R + 1` exceeds in
depth by more than `1/(8b)`.  The edge weight gains `e^{2δb}` over `∫|f|²`.  The root-killing
factor, selected by halving (`cluster_selection_radius`), costs `relaxedRootRatio`, polynomial
in `a` to the power `n` (the window count).  The zeros beyond ordinate `R` are paid for by
`(1 + R)^M ≥ e^b`.

* `re_W_le_of_profile`: the Weil form of any real-structured profile, with the deep pair counted
  exactly, the window zeros of sign `Re Ψ² ≤ 0`, and a weighted tail.
* `exists_penalized_deepest_zero`: maximizing `Re ρ - λ|Im ρ - γ₀|` selects a zero whose
  neighbours within `R'` are at most `λR'` deeper.
* `relaxed_test_package`: the test and its five estimates.
* `exists_relaxed_violation`: the explicit criterion.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-- **Weil form of a real-structured profile.**  Suppose the Weil summand of `f` is
`m_ρ Ψ(γ_ρ - γ₁)²`, `Ψ(z̄) = conj Ψ(z)`, `ρ₁ = ½ + δ₁ + iγ₁` is a zero with `Ψ(-iδ₁)` purely
imaginary, every other zero of the window `|γ - γ₁| ≤ H` has `Re Ψ² ≤ 0`, and every zero outside the
window has `|Ψ|² (1 + |γ - γ₁|)^{3+E} ≤ C₁`.  Then `Re W(f,f) ≤ -2|Ψ(-iδ₁)|² + C₁ 24A₀
log(|γ₁| + 3)/(1 + H)^E`. -/
theorem re_W_le_of_profile (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {f : ℝ → ℂ} {Ψ : ℂ → ℂ} {γ₁ : ℝ}
    (hWs : ∀ ρ : ℂ, Z.Wsummand f f ρ = (Z.mult ρ : ℂ) * Ψ (gammaOf ρ - γ₁) ^ 2)
    (hconj : ∀ z, Ψ (conj z) = conj (Ψ z))
    {ρ₁ : ℂ} (hρ₁ : ρ₁ ∈ Z.carrier) {δ₁ : ℝ} (hδ₁ : 0 < δ₁) (hre : ρ₁.re = 1 / 2 + δ₁)
    (him : ρ₁.im = γ₁) {H : ℝ} (hH : 0 < H) {Wn : Finset ℂ}
    (hWn : ∀ ρ, ρ ∈ Wn ↔ ρ ∈ Z.carrier ∧ γ₁ - H < ρ.im ∧ ρ.im ≤ γ₁ + H)
    (hwin : ∀ ρ ∈ Wn, (Ψ (gammaOf ρ - γ₁) ^ 2).re ≤ 0)
    (hsq : Ψ (-(I * δ₁)) ^ 2 = -((‖Ψ (-(I * δ₁))‖ ^ 2 : ℝ) : ℂ))
    {E : ℕ} {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (htail : ∀ ρ ∈ Z.carrier, ρ ∉ Wn →
      ‖Ψ (gammaOf ρ - γ₁)‖ ^ 2 * (1 + |ρ.im - γ₁|) ^ (3 + E) ≤ C₁) :
    (Z.W f f).re ≤ -2 * ‖Ψ (-(I * δ₁))‖ ^ 2 +
      C₁ / (1 + H) ^ E * (24 * A₀ * Real.log (|γ₁| + 3)) := by
  classical
  obtain ⟨hwsum, hwle⟩ := window_tsum_le Z hA₀ hloc γ₁
  set Ψ₁ := Ψ (-(I * (δ₁ : ℂ))) with hΨ₁
  have hH1 : 0 < 1 + H := by linarith
  -- window facts
  have hρ₁W : ρ₁ ∈ Wn := (hWn ρ₁).mpr ⟨hρ₁, by rw [him]; linarith, by rw [him]; linarith⟩
  have hrefl_im : (reflect ρ₁).im = ρ₁.im := by
    simp only [reflect, Complex.sub_im, Complex.one_im, Complex.conj_im]; ring
  have hρ₂W : reflect ρ₁ ∈ Wn :=
    (hWn _).mpr ⟨Z.reflect_mem ρ₁ hρ₁, by rw [hrefl_im, him]; linarith,
      by rw [hrefl_im, him]; linarith⟩
  have hne : (⟨reflect ρ₁, Z.reflect_mem ρ₁ hρ₁⟩ : Z.carrier) ≠ ⟨ρ₁, hρ₁⟩ := by
    intro h
    have := congrArg (fun x : Z.carrier => (x : ℂ).re) h
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re, hre] at this
    linarith
  have hx₁ : gammaOf ρ₁ - γ₁ = -(I * δ₁) := (gammaOf_sub_of_re_im him hre).1
  have hx₂ : gammaOf (reflect ρ₁) - γ₁ = conj (-(I * (δ₁ : ℂ))) := by
    rw [← him, gammaOf_sub_reflect hre]; simp [Complex.conj_ofReal]
  -- outside the window
  have hout : ∀ ρ : Z.carrier, (ρ : ℂ) ∉ Wn → H ≤ |(ρ : ℂ).im - γ₁| := by
    intro ρ hρ
    have hnot : ¬ (γ₁ - H < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ γ₁ + H) := fun h =>
      hρ ((hWn _).mpr ⟨ρ.2, h⟩)
    rw [not_and_or, not_lt, not_le] at hnot
    rcases hnot with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hnorm_out : ∀ ρ : Z.carrier, (ρ : ℂ) ∉ Wn →
      ‖Z.Wsummand f f ρ‖ ≤ (Z.mult (ρ : ℂ) : ℝ) * C₁ /
        ((1 + H) ^ E * (1 + |(ρ : ℂ).im - γ₁|) ^ 3) := by
    intro ρ hρ
    have hD1 : 1 + H ≤ 1 + |(ρ : ℂ).im - γ₁| := by linarith [hout ρ hρ]
    have hD0 : 0 < 1 + |(ρ : ℂ).im - γ₁| := by linarith [abs_nonneg ((ρ : ℂ).im - γ₁)]
    have hDE : (1 + H) ^ E * (1 + |(ρ : ℂ).im - γ₁|) ^ 3 ≤ (1 + |(ρ : ℂ).im - γ₁|) ^ (3 + E) := by
      rw [pow_add, mul_comm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH1.le hD1 E) (by positivity)
    have ht := htail ρ ρ.2 hρ
    have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
    rw [hWs, norm_mul, norm_pow, Complex.norm_natCast]
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hm
    rw [le_div_iff₀ (by positivity)]
    calc ‖Ψ (gammaOf ρ - γ₁)‖ ^ 2 * ((1 + H) ^ E * (1 + |(ρ : ℂ).im - γ₁|) ^ 3)
        ≤ ‖Ψ (gammaOf ρ - γ₁)‖ ^ 2 * (1 + |(ρ : ℂ).im - γ₁|) ^ (3 + E) :=
          mul_le_mul_of_nonneg_left hDE (sq_nonneg _)
      _ ≤ C₁ := ht
  -- summability
  have hsum : Summable (fun ρ : Z.carrier => Z.Wsummand f f ρ) := by
    refine Summable.of_norm_bounded_eventually (hwsum.mul_left (C₁ / (1 + H) ^ E)) ?_
    have hfin : {ρ : Z.carrier | (ρ : ℂ) ∈ Wn}.Finite :=
      (Wn.finite_toSet.preimage Subtype.val_injective.injOn)
    filter_upwards [hfin.compl_mem_cofinite] with ρ hρ
    have hρ' : (ρ : ℂ) ∉ Wn := hρ
    refine (hnorm_out ρ hρ').trans (le_of_eq ?_)
    field_simp
  -- the pointwise bound
  set Q := (Z.mult ρ₁ : ℝ) * ‖Ψ₁‖ ^ 2 with hQ
  have hpt : ∀ ρ : Z.carrier, (Z.Wsummand f f ρ).re ≤
      (if ρ = ⟨ρ₁, hρ₁⟩ then -Q else 0) +
        (if ρ = ⟨reflect ρ₁, Z.reflect_mem ρ₁ hρ₁⟩ then -Q else 0) +
        lowHeightTail Z Wn γ₁ H C₁ E ρ := by
    intro ρ
    have hre_eq : (Z.Wsummand f f ρ).re =
        (Z.mult (ρ : ℂ) : ℝ) * (Ψ (gammaOf ρ - γ₁) ^ 2).re := by
      rw [hWs]; simp [Complex.mul_re]
    by_cases h0 : ρ = ⟨ρ₁, hρ₁⟩
    · subst h0
      rw [if_pos rfl, if_neg hne.symm]
      simp only [lowHeightTail, hρ₁W, if_true, add_zero]
      rw [hre_eq, show ((⟨ρ₁, hρ₁⟩ : Z.carrier) : ℂ) = ρ₁ from rfl, hx₁, ← hΨ₁, hsq]
      simp [hQ, -Complex.ofReal_pow]
    by_cases h1 : ρ = ⟨reflect ρ₁, Z.reflect_mem ρ₁ hρ₁⟩
    · subst h1
      rw [if_neg hne, if_pos rfl]
      simp only [lowHeightTail, hρ₂W, if_true, add_zero, zero_add]
      rw [hre_eq, show ((⟨reflect ρ₁, Z.reflect_mem ρ₁ hρ₁⟩ : Z.carrier) : ℂ) = reflect ρ₁ from rfl,
        hx₂, hconj, ← hΨ₁, ← map_pow, hsq, Z.mult_reflect ρ₁ hρ₁]
      simp [hQ, -Complex.ofReal_pow]
    rw [if_neg h0, if_neg h1, zero_add, zero_add]
    have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
    by_cases hW : (ρ : ℂ) ∈ Wn
    · simp only [lowHeightTail, hW, if_true]
      rw [hre_eq]
      exact mul_nonpos_of_nonneg_of_nonpos hm (hwin _ hW)
    · simp only [lowHeightTail, hW, if_false]
      refine (Complex.re_le_norm _).trans ((hnorm_out ρ hW).trans (le_of_eq ?_))
      ring
  have hTs : Summable (lowHeightTail Z Wn γ₁ H C₁ E) := by
    refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) (hwsum.mul_left (C₁ / (1 + H) ^ E))
    · unfold lowHeightTail; split_ifs
      · exact le_rfl
      · have : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
        positivity
    · unfold lowHeightTail; split_ifs
      · have : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
        positivity
      · apply le_of_eq; field_simp
  have hW := re_W_le_of_pointwise Z f hsum _ _ Q hTs hpt
  have hTle : ∑' ρ, lowHeightTail Z Wn γ₁ H C₁ E ρ ≤ C₁ / (1 + H) ^ E *
      (24 * A₀ * Real.log (|γ₁| + 3)) := by
    have hcomp : ∀ ρ, lowHeightTail Z Wn γ₁ H C₁ E ρ ≤
        C₁ / (1 + H) ^ E * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₁|) ^ 3) := by
      intro ρ
      unfold lowHeightTail; split_ifs
      · have : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
        positivity
      · apply le_of_eq; field_simp
    calc ∑' ρ, lowHeightTail Z Wn γ₁ H C₁ E ρ
        ≤ ∑' ρ : Z.carrier, C₁ / (1 + H) ^ E * ((Z.mult (ρ : ℂ) : ℝ) /
            (1 + |(ρ : ℂ).im - γ₁|) ^ 3) :=
          Summable.tsum_le_tsum hcomp hTs (hwsum.mul_left _)
      _ = C₁ / (1 + H) ^ E * ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₁|) ^ 3 :=
          tsum_mul_left
      _ ≤ C₁ / (1 + H) ^ E * (24 * A₀ * Real.log (|γ₁| + 3)) :=
          mul_le_mul_of_nonneg_left hwle (by positivity)
  have hm : (1 : ℝ) ≤ Z.mult ρ₁ := by exact_mod_cast Z.one_le_mult ρ₁ hρ₁
  have hFn := sq_nonneg ‖Ψ₁‖
  have : -2 * Q ≤ -2 * ‖Ψ₁‖ ^ 2 := by rw [hQ]; nlinarith
  linarith


/-! ### The penalized deepest zero -/

/-- **Penalized deepest zero.**  For `λ > 0` and a zero `ρ₀` with `Re ρ₀ ≥ ½`, some zero `ρ*`
maximizes `Re ρ - λ|Im ρ - Im ρ₀|` among the zeros with `|Im ρ - Im ρ₀| ≤ D`, `D ≥ 1/(2λ) + R'`.
Then `Re ρ* ≥ Re ρ₀`, `|Im ρ* - Im ρ₀| ≤ 1/(2λ)`, and every zero within ordinate `R'` of `ρ*` has
`|Re ρ - ½| ≤ (Re ρ* - ½) + λR'`. -/
theorem exists_penalized_deepest_zero (Z : ZeroConfig) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hhalf : 1 / 2 ≤ ρ₀.re) {lam R' : ℝ} (hlam : 0 < lam) (hR' : 0 ≤ R') :
    ∃ ρs ∈ Z.carrier, ρ₀.re ≤ ρs.re ∧ |ρs.im - ρ₀.im| ≤ 1 / (2 * lam) ∧
      ∀ ρ ∈ Z.carrier, |ρ.im - ρs.im| ≤ R' → |ρ.re - 1 / 2| ≤ (ρs.re - 1 / 2) + lam * R' := by
  classical
  set D := 1 / (2 * lam) + R' + 1 with hD
  set W := (Z.finite_window (ρ₀.im - D) (ρ₀.im + D)).toFinset with hWdef
  have hW : ∀ ρ, ρ ∈ W ↔ ρ ∈ Z.carrier ∧ ρ₀.im - D < ρ.im ∧ ρ.im ≤ ρ₀.im + D := by
    intro ρ; rw [hWdef, Set.Finite.mem_toFinset]; rfl
  have hD0 : 0 < D := by rw [hD]; positivity
  have hρ₀W : ρ₀ ∈ W := (hW ρ₀).mpr ⟨hρ₀, by linarith, by linarith⟩
  set φ : ℂ → ℝ := fun ρ => ρ.re - lam * |ρ.im - ρ₀.im| with hφ
  obtain ⟨ρs, hρsW, hmax⟩ := W.exists_max_image φ ⟨ρ₀, hρ₀W⟩
  obtain ⟨hρsZ, -, -⟩ := (hW ρs).mp hρsW
  have hφ₀ : φ ρ₀ = ρ₀.re := by simp [hφ]
  have hge : ρ₀.re ≤ φ ρs := hφ₀ ▸ hmax ρ₀ hρ₀W
  have hst := Z.strip ρs hρsZ
  have habs0 := abs_nonneg (ρs.im - ρ₀.im)
  have hre_ge : ρ₀.re ≤ ρs.re := by
    have : φ ρs ≤ ρs.re := by
      simp only [hφ]; nlinarith
    linarith
  have hdist : |ρs.im - ρ₀.im| ≤ 1 / (2 * lam) := by
    have h1 : lam * |ρs.im - ρ₀.im| ≤ 1 / 2 := by
      simp only [hφ] at hge; linarith [hst.2]
    rw [le_div_iff₀ (by positivity)]
    linarith
  refine ⟨ρs, hρsZ, hre_ge, hdist, fun ρ hρ hρR => ?_⟩
  -- `ρ` and its reflection lie in the window
  have hin : ∀ σ ∈ Z.carrier, σ.im = ρ.im → σ ∈ W := by
    intro σ hσ hσim
    refine (hW σ).mpr ⟨hσ, ?_, ?_⟩ <;>
    · have h1 := abs_le.mp hρR
      have h2 := abs_le.mp hdist
      rw [hσim]; linarith
  have hbound : ∀ σ ∈ Z.carrier, σ.im = ρ.im → σ.re ≤ ρs.re + lam * R' := by
    intro σ hσ hσim
    have h := hmax σ (hin σ hσ hσim)
    simp only [hφ] at h
    have htri : |ρ.im - ρ₀.im| ≤ |ρ.im - ρs.im| + |ρs.im - ρ₀.im| := by
      have := abs_sub_le ρ.im ρs.im ρ₀.im; linarith
    rw [hσim] at h
    nlinarith
  have h1 := hbound ρ hρ rfl
  have h2 := hbound (reflect ρ) (Z.reflect_mem ρ hρ) (Tail.reflect_im ρ)
  have hrr : (reflect ρ).re = 1 - ρ.re := by
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
  rw [hrr] at h2
  rw [abs_le]; constructor <;> linarith


/-! ### Bounds for the relaxed criterion -/

theorem list_prod_map_le_pow_of_le {l : List ℂ} {f : ℂ → ℝ} {C : ℝ}
    (hf0 : ∀ r ∈ l, 0 ≤ f r) (hf : ∀ r ∈ l, f r ≤ C) : (l.map f).prod ≤ C ^ l.length := by
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    have h0 : 0 ≤ (l.map f).prod := List.prod_nonneg fun y hy => by
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hy; exact hf0 r' (List.mem_cons_of_mem r hr')
    have hr := hf r List.mem_cons_self
    have hC : 0 ≤ C := le_trans (hf0 r List.mem_cons_self) hr
    rw [mul_comm (C ^ l.length) C]
    exact mul_le_mul hr (ih (fun r' h => hf0 r' (List.mem_cons_of_mem r h))
      (fun r' h => hf r' (List.mem_cons_of_mem r h))) h0 hC

/-- The killing-root ratio of the low-height roots is at most `(122/η)^{2n} (495/δ)²`. -/
theorem rootRatio_lowHeightRoots_le (Z : ZeroConfig) {γ₁ c δ η : ℝ} {Kset : Finset ℂ} {n : ℕ}
    (hδ : 0 < δ) (hη0 : 0 < η) (hη1 : η ≤ 1) (hγ : 1 ≤ |γ₁|) (hc : c ∈ Icc (-δ) δ)
    (hδ2 : δ ≤ 1 / 2)
    (hK : ∀ ρ ∈ Kset, ρ ∈ Z.carrier ∧ |ρ.im - γ₁| ≤ 100) (hKn : Kset.card ≤ n)
    (hkil : ∀ ρ ∈ Kset, η ≤ ‖(gammaOf ρ - γ₁) - -(I * δ)‖ ∧ η ≤ ‖(gammaOf ρ - γ₁) - I * δ‖) :
    ((pairRoots (lowHeightRoots γ₁ c Kset)).map fun r =>
        (unitDerivL1 + ‖r‖ * unitL1) / (unitL1 * ‖-(I * (δ : ℂ)) - r‖)).prod ≤
      (122 / η) ^ (2 * n) * (495 / δ) ^ 2 := by
  have hm0 := unitL1_pos
  have hm0' : (48 / 100 : ℝ) ≤ unitL1 := unitWeightFloor_ge.trans unitWeightFloor_le_unitL1
  have hm1 := unitDerivL1_le
  have hm10 := unitDerivL1_nonneg
  set q : ℂ → ℝ := fun r => (unitDerivL1 + ‖r‖ * unitL1) / (unitL1 * ‖-(I * (δ : ℂ)) - r‖) with hq
  have hq0 : ∀ r, 0 ≤ q r := fun r => by simp only [hq]; positivity
  -- a factor with `‖r‖ ≤ B` and `‖x₀ - r‖ ≥ d`
  have hfac : ∀ r : ℂ, ∀ B d : ℝ, 0 < d → ‖r‖ ≤ B → d ≤ ‖-(I * (δ : ℂ)) - r‖ →
      q r ≤ (unitDerivL1 / unitL1 + B) / d := by
    intro r B d hd hrB hrd
    simp only [hq]
    have hpos : 0 < ‖-(I * (δ : ℂ)) - r‖ := lt_of_lt_of_le hd hrd
    rw [div_le_div_iff₀ (by positivity) hd]
    have h1 : (unitDerivL1 + ‖r‖ * unitL1) * d ≤ (unitDerivL1 + B * unitL1) * ‖-(I * (δ : ℂ)) - r‖ := by
      have hB : unitDerivL1 + ‖r‖ * unitL1 ≤ unitDerivL1 + B * unitL1 := by
        have := mul_le_mul_of_nonneg_right hrB hm0.le; linarith
      have hB0 : 0 ≤ unitDerivL1 + ‖r‖ * unitL1 := by positivity
      exact mul_le_mul hB hrd hd.le (le_trans hB0 hB)
    have e : (unitDerivL1 / unitL1 + B) * (unitL1 * ‖-(I * (δ : ℂ)) - r‖) =
        (unitDerivL1 + B * unitL1) * ‖-(I * (δ : ℂ)) - r‖ := by field_simp
    rw [e]; exact h1
  have hr1 : unitDerivL1 / unitL1 ≤ 21 := by
    rw [div_le_iff₀ hm0]; nlinarith
  unfold lowHeightRoots
  rw [pairRoots_append, pairRoots_pc, List.map_append, List.prod_append]
  -- the killed roots
  have hKpart : ((pairRoots (Kset.toList.map fun ρ => gammaOf ρ - γ₁)).map q).prod ≤
      (122 / η) ^ (2 * n) := by
    have hle : ∀ r ∈ pairRoots (Kset.toList.map fun ρ => gammaOf ρ - γ₁), q r ≤ 122 / η := by
      intro r hr
      obtain ⟨s, hs, hrs⟩ := mem_pairRoots.mp hr
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hs
      obtain ⟨hρZ, hρH⟩ := hK ρ (Finset.mem_toList.mp hρ)
      obtain ⟨h1, h2⟩ := hkil ρ (Finset.mem_toList.mp hρ)
      have hst := Z.strip ρ hρZ
      have hnorm : ‖gammaOf ρ - γ₁‖ ≤ 101 := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        rw [Complex.sub_re, WeilEF.gammaOf_re, Complex.ofReal_re, Complex.sub_im,
          WeilEF.gammaOf_im, Complex.ofReal_im, sub_zero]
        have : |1 / 2 - ρ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hst.1, hst.2]
        linarith
      rcases hrs with rfl | rfl
      · have hd : η ≤ ‖-(I * (δ : ℂ)) - (gammaOf ρ - γ₁)‖ := by rw [norm_sub_rev]; exact h1
        refine (hfac _ 101 η hη0 hnorm hd).trans ?_
        rw [div_le_div_iff_of_pos_right hη0]; linarith
      · have hd : η ≤ ‖-(I * (δ : ℂ)) - conj (gammaOf ρ - γ₁)‖ := by
          have : -(I * (δ : ℂ)) - conj (gammaOf ρ - γ₁) = conj (I * δ - (gammaOf ρ - γ₁)) := by
            simp [map_sub, Complex.conj_ofReal]
          rw [this, Complex.norm_conj, norm_sub_rev]; exact h2
        refine (hfac _ 101 η hη0 (by rw [Complex.norm_conj]; exact hnorm) hd).trans ?_
        rw [div_le_div_iff_of_pos_right hη0]; linarith
    have hge1 : 1 ≤ 122 / η := by rw [le_div_iff₀ hη0]; linarith
    refine (list_prod_map_le_pow_of_le (fun r _ => hq0 r) hle).trans ?_
    rw [pairRoots_length, List.length_map, Finset.length_toList]
    exact pow_le_pow_right₀ hge1 (by omega)
  -- the polar and phase roots
  have hp : q (⟨-γ₁, 1 / 2⟩ : ℂ) ≤ 45 / 2 := by
    have hd : |γ₁| ≤ ‖-(I * (δ : ℂ)) - (⟨-γ₁, 1 / 2⟩ : ℂ)‖ := by
      have := Complex.abs_re_le_norm (-(I * (δ : ℂ)) - (⟨-γ₁, 1 / 2⟩ : ℂ))
      simpa using this
    have hn : ‖(⟨-γ₁, 1 / 2⟩ : ℂ)‖ ≤ |γ₁| + 1 / 2 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_; norm_num [abs_of_pos]
    refine (hfac _ _ _ (by linarith) hn hd).trans ?_
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hp' : q (conj (⟨-γ₁, 1 / 2⟩ : ℂ)) ≤ 45 / 2 := by
    have hd : |γ₁| ≤ ‖-(I * (δ : ℂ)) - conj (⟨-γ₁, 1 / 2⟩ : ℂ)‖ := by
      have := Complex.abs_re_le_norm (-(I * (δ : ℂ)) - conj (⟨-γ₁, 1 / 2⟩ : ℂ))
      simpa using this
    have hn : ‖conj (⟨-γ₁, 1 / 2⟩ : ℂ)‖ ≤ |γ₁| + 1 / 2 := by
      rw [Complex.norm_conj]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_; norm_num [abs_of_pos]
    refine (hfac _ _ _ (by linarith) hn hd).trans ?_
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hcabs : |c| ≤ 1 / 2 := (abs_le.mpr hc).trans hδ2
  have hcd : δ ≤ ‖-(I * (δ : ℂ)) - (c : ℂ)‖ := by
    have := Complex.abs_im_le_norm (-(I * (δ : ℂ)) - (c : ℂ))
    simpa [abs_of_pos hδ] using this
  have hcn : ‖(c : ℂ)‖ ≤ 1 / 2 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hcabs
  have hq_c : q (c : ℂ) ≤ 22 / δ := by
    refine (hfac _ _ _ hδ hcn hcd).trans ?_
    rw [div_le_div_iff_of_pos_right hδ]; linarith
  have hq_c' : q (conj (c : ℂ)) ≤ 22 / δ := by rw [Complex.conj_ofReal]; exact hq_c
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have e : (495 / δ) ^ 2 = 45 / 2 * (45 / 2 * (22 / δ * (22 / δ))) := by ring
  rw [e]
  have hK0 : 0 ≤ ((pairRoots (Kset.toList.map fun ρ => gammaOf ρ - γ₁)).map q).prod :=
    List.prod_nonneg fun y hy => by obtain ⟨r, -, rfl⟩ := List.mem_map.mp hy; exact hq0 r
  gcongr


theorem four_testNorm_sinhTest_sq_le {b δ : ℝ} (hb : 1 ≤ b) (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2) :
    (4 * testNorm (sinhTest b δ)) ^ 2 ≤ 46656 * b ^ 12 * Real.exp (2 * δ * b) := by
  have hb0 : 0 ≤ b := by linarith
  have hbpos : 0 < b := by linarith
  have ht := testNorm_sinhTest_le hb0 hδ0
  have hcosh := cosh_le_exp_self_of_nonneg (show 0 ≤ δ * b by positivity)
  have hb3 : b ^ 3 ≤ b ^ 5 := pow_le_pow_right₀ hb (by norm_num)
  have hb4 : b ^ 4 ≤ b ^ 5 := pow_le_pow_right₀ hb (by norm_num)
  have hpoly : b ^ 5 + δ ^ 2 * b ^ 5 + 10 * δ * b ^ 4 + 20 * b ^ 3 ≤ 27 * b ^ 5 := by
    have hp5 : 0 < b ^ 5 := by positivity
    have hp4 : 0 ≤ b ^ 4 := by positivity
    have hδsq : δ ^ 2 ≤ 1 := by nlinarith
    have h1 : δ ^ 2 * b ^ 5 ≤ b ^ 5 := by nlinarith
    have h2 : 10 * δ * b ^ 4 ≤ 5 * b ^ 5 := by nlinarith
    nlinarith
  have htn : testNorm (sinhTest b δ) ≤ 54 * b ^ 6 * Real.exp (δ * b) := by
    refine ht.trans ?_
    calc 2 * b * Real.cosh (δ * b) * (b ^ 5 + δ ^ 2 * b ^ 5 + 10 * δ * b ^ 4 + 20 * b ^ 3)
        ≤ 2 * b * Real.exp (δ * b) * (27 * b ^ 5) := by
          have : 0 ≤ b ^ 5 + δ ^ 2 * b ^ 5 + 10 * δ * b ^ 4 + 20 * b ^ 3 := by positivity
          gcongr
      _ = 54 * b ^ 6 * Real.exp (δ * b) := by ring
  have h0 := testNorm_nonneg (sinhTest b δ)
  have hsq := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left htn (by norm_num : (0:ℝ) ≤ 4)) 2
  calc (4 * testNorm (sinhTest b δ)) ^ 2 ≤ (4 * (54 * b ^ 6 * Real.exp (δ * b))) ^ 2 := hsq
    _ = 46656 * b ^ 12 * (Real.exp (δ * b) * Real.exp (δ * b)) := by ring
    _ = 46656 * b ^ 12 * Real.exp (2 * δ * b) := by rw [← Real.exp_add]; ring_nf

/-! ### The relaxed Hodge index -/

/-- **The relaxed Hodge index at level `a` with exponent `θ`:** `Re W(f, f) ≥ -e^{θa} ∫ |f|²` for
every polar-constrained `C²` test supported in `[-a, a]`. -/
def RelaxedHodgeIndexAtLevel (Z : ZeroConfig) (θ a : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → paperFT f (I / 2) = 0 →
    paperFT f (-(I / 2)) = 0 → -(Real.exp (θ * a) * ∫ u, ‖f u‖ ^ 2) ≤ (Z.W f f).re

theorem relaxedHodgeIndexAtLevel_of_hodgeIndex {Z : ZeroConfig} {a : ℝ}
    (h : HodgeIndexAtLevel Z a) (θ : ℝ) : RelaxedHodgeIndexAtLevel Z θ a := by
  intro f hf hfs hp hm
  have := h f hf hfs hp hm
  have : 0 ≤ Real.exp (θ * a) * ∫ u, ‖f u‖ ^ 2 :=
    mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => sq_nonneg _)
  linarith

/-- The killing distance of the relaxed construction: the halving radius
`r₀ = min(ε₀, 1/(10⁵ b⁵))` divided by `2(4λ)^{⌊log₂ n⌋+1}`. -/
def relaxedKillScale (δ b : ℝ) (M n : ℕ) : ℝ :=
  min (lowHeightEps0 δ M) (1 / (10 ^ 5 * b ^ 5)) /
    (2 * (4 * lowHeightScale n) ^ (Nat.log 2 n + 1))

/-- The root ratio `(122/η)^{2n}(990/δ)²` of the relaxed construction. -/
def relaxedRootRatio (δ b : ℝ) (M n : ℕ) : ℝ :=
  (122 / relaxedKillScale δ b M n) ^ (2 * n) * (990 / δ) ^ 2

theorem relaxedKillScale_pos {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) (M n : ℕ) :
    0 < relaxedKillScale δ b M n := by
  unfold relaxedKillScale lowHeightScale
  have := lowHeightEps0_pos hδ M
  have : 0 < min (lowHeightEps0 δ M) (1 / (10 ^ 5 * b ^ 5)) := lt_min this (by positivity)
  positivity


/-! ### Window and tail of the edge profile -/

/-- The window zeros of the relaxed test contribute `Re Ψ² ≤ 0`: the killed ones vanish, the
cluster ones are controlled by `re_sq_edgeProfile_nonpos`. -/
theorem edge_window_nonpos {γ₁ c δ₁ b ε η : ℝ} {Kset Wn : Finset ℂ} {k n : ℕ}
    (hδ₁ : 0 < δ₁) (hδ₁2 : δ₁ ≤ 1 / 2) (hγ : 1 ≤ |γ₁|) (hb4 : 4 ≤ b)
    (hδ₁b : 1 / 2 ≤ δ₁ * (b - 2)) (hKn : Kset.card ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hεb : ε * (10 ^ 5 * b ^ 5) ≤ 1) (hη0 : 0 < η)
    (hclu : ∀ ρ ∈ Wn, ρ ∉ Kset →
      ‖(gammaOf ρ - γ₁) - -(I * δ₁)‖ < ε ∨ ‖(gammaOf ρ - γ₁) - I * δ₁‖ < ε)
    (hkil : ∀ ρ ∈ Kset,
      η ≤ ‖(gammaOf ρ - γ₁) - -(I * δ₁)‖ ∧ η ≤ ‖(gammaOf ρ - γ₁) - I * δ₁‖)
    {N₀ : ℕ} (hS : (N₀ : ℝ) * (4 * ε) + (2 * (n : ℝ)) * (ε / η) + 2 * ε + 2 * ε / δ₁ ≤ 1 / 20)
    (hk : k + 2 * (lowHeightRoots γ₁ c Kset).length + 1 = N₀)
    (hsq : edgeProfile b δ₁ k (lowHeightRoots γ₁ c Kset) (-(I * δ₁)) ^ 2 =
      -((‖edgeProfile b δ₁ k (lowHeightRoots γ₁ c Kset) (-(I * δ₁))‖ ^ 2 : ℝ) : ℂ)) :
    ∀ ρ ∈ Wn, (edgeProfile b δ₁ k (lowHeightRoots γ₁ c Kset) (gammaOf ρ - γ₁) ^ 2).re ≤ 0 := by
  classical
  set L := lowHeightRoots γ₁ c Kset with hL
  set x₀ : ℂ := -(I * δ₁) with hx₀
  have hb0 : 0 ≤ b := by linarith
  have hr := ne_of_pairRoots_lowHeightRoots (c := c) hδ₁ hη0 hγ hkil
  have hsum := sum_pairRoots_lowHeightRoots_le (c := c) hδ₁ hε0.le hη0 hγ hkil
  have hS' : ((k + 2 * L.length + 1 : ℕ) : ℝ) * (4 * ε) +
      ((pairRoots L).map fun r => ε / ‖-(I * δ₁) - r‖).sum ≤ 1 / 20 := by
    rw [hk]
    have hcard : (2 * (Kset.card : ℝ)) * (ε / η) ≤ (2 * (n : ℝ)) * (ε / η) := by
      have : (Kset.card : ℝ) ≤ n := by exact_mod_cast hKn
      have : 0 ≤ ε / η := by positivity
      nlinarith
    linarith
  -- the edge transform at `x₀` is the real energy `P ≥ 0`
  set P := ∫ u, sinhTest b δ₁ u * Real.sinh (δ₁ * u) with hP
  have hP0 : 0 ≤ P := by
    have := sinhTest_energy_ge_exp hb4 hδ₁ hδ₁b
    exact le_trans (by positivity) this
  have hs₀ : paperFT (fun u => (sinhTest b δ₁ u : ℂ)) x₀ = (P : ℂ) :=
    paperFT_odd_neg_I_mul (sinhTest_contDiff b δ₁).continuous (sinhTest_supp hb0)
      (sinhTest_odd b δ₁) δ₁
  have hs₀n : ‖paperFT (fun u => (sinhTest b δ₁ u : ℂ)) x₀‖ = P := by
    rw [hs₀, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP0]
  have hclus : ∀ z, ‖z - x₀‖ < ε → (edgeProfile b δ₁ k L z ^ 2).re ≤ 0 := by
    intro z hz
    have hG := norm_lowHeightProfile_sub_le_tenth hδ₁ hδ₁2 hε0 hε1 hr hS' hz
    have hs := norm_paperFT_sinhTest_sub_le hb4 hδ₁ hδ₁2 hδ₁b hε0.le hεb hz.le
    rw [← hP, ← hs₀n] at hs
    exact re_sq_edgeProfile_nonpos hG hs hsq
  intro ρ hρ
  by_cases hK : ρ ∈ Kset
  · have hmem : gammaOf ρ - γ₁ ∈ L := by
      rw [hL]; unfold lowHeightRoots
      exact List.mem_append_left _ (List.mem_map.mpr ⟨ρ, Finset.mem_toList.mpr hK, rfl⟩)
    have : lowHeightProfile (sinhTestWeight 1) k L (gammaOf ρ - γ₁) = 0 :=
      lowHeightProfile_eq_zero_of_mem hmem
    simp [edgeProfile, this]
  · rcases hclu ρ hρ hK with h | h
    · exact hclus _ h
    · have h2 : ‖conj (gammaOf ρ - γ₁) - x₀‖ < ε := by
        have : conj (gammaOf ρ - γ₁) - x₀ = conj ((gammaOf ρ - γ₁) - I * δ₁) := by
          simp [hx₀, map_sub, Complex.conj_ofReal]
        rw [this, Complex.norm_conj]; exact h
      have h3 := hclus _ h2
      rw [edgeProfile_conj, ← map_pow, Complex.conj_re] at h3
      exact h3

/-- The tail of the relaxed test: zeros within ordinate `R` of the centre are at most `1/(4b)`
deeper than it; zeros beyond `R` are paid for by `(1 + R)^M ≥ e^b`. -/
theorem edge_tail_bound (Z : ZeroConfig) {γ₁ c δ₁ b R : ℝ} {Kset : Finset ℂ} {k M n : ℕ}
    (hb : 0 < b) (hc : c ∈ Icc (-δ₁) δ₁) (hδ₁2 : δ₁ ≤ 1 / 2)
    (hK : ∀ ρ ∈ Kset, ρ ∈ Z.carrier ∧ |ρ.im - γ₁| ≤ 100)
    (hk : k + 2 * (lowHeightRoots γ₁ c Kset).length + 1 = M) (hKn : Kset.card ≤ n)
    (hM : 2 * n + 7 ≤ M) (hR : 0 ≤ R) (hRM : Real.exp b ≤ (1 + R) ^ M)
    (hnear : ∀ ρ ∈ Z.carrier, |ρ.im - γ₁| ≤ R → |ρ.re - 1 / 2| ≤ δ₁ + 1 / (4 * b)) :
    ∀ ρ ∈ Z.carrier,
      ‖edgeProfile b δ₁ k (lowHeightRoots γ₁ c Kset) (gammaOf ρ - γ₁)‖ ^ 2 *
        (1 + |ρ.im - γ₁|) ^ (3 + (3 * M - 4 * n - 11)) ≤
      Real.exp (2 * δ₁ * b + 1 / 2) * (4 * testNorm (sinhTest b δ₁)) ^ 2 *
        clusterTailConstant 100 |γ₁| M n := by
  intro ρ hρ
  set x := gammaOf ρ - γ₁ with hxdef
  have hst := Z.strip ρ hρ
  have hxre : x.re = ρ.im - γ₁ := by simp [hxdef, WeilEF.gammaOf_re]
  have hxim : |x.im| = |ρ.re - 1 / 2| := by
    rw [hxdef, Complex.sub_im, WeilEF.gammaOf_im, Complex.ofReal_im, sub_zero, abs_sub_comm]
  have hx : |x.im| ≤ 1 / 2 := by
    rw [hxim, abs_le]; constructor <;> linarith [hst.1, hst.2]
  have hG := lowHeight_tail_bound_split Z (by norm_num : (1 : ℝ) / 2 ≤ 100) hc hδ₁2 hK hk hKn
    (E := 4 * M - 4 * n - 11) (by omega) x hx
  have hΨ := norm_sq_edgeProfile_tail_le (δ := δ₁) hb.le hG
  rw [hxre] at hΨ
  set T := (4 * testNorm (sinhTest b δ₁)) ^ 2 * clusterTailConstant 100 |γ₁| M n with hTdef
  have hT0 : 0 ≤ T := by
    have : 0 ≤ clusterTailConstant 100 |γ₁| M n := by unfold clusterTailConstant; positivity
    positivity
  have hsplit : (4 * M - 4 * n - 11) = (3 * M - 4 * n - 11) + M := by omega
  set D := 1 + |ρ.im - γ₁| with hD
  have hD1 : 1 ≤ D := by linarith [abs_nonneg (ρ.im - γ₁)]
  have hΨ' : ‖edgeProfile b δ₁ k (lowHeightRoots γ₁ c Kset) x‖ ^ 2 * D ^ (3 + (3 * M - 4 * n - 11)) *
      D ^ M ≤ Real.exp (2 * |x.im| * b) * T := by
    calc _ = ‖edgeProfile b δ₁ k (lowHeightRoots γ₁ c Kset) x‖ ^ 2 * D ^ (3 + (4 * M - 4 * n - 11)) := by
          rw [hsplit, show 3 + ((3 * M - 4 * n - 11) + M) = (3 + (3 * M - 4 * n - 11)) + M by ring,
            pow_add]; ring
      _ ≤ _ := by rw [hTdef]; linarith [hΨ]
  have hF0 : 0 ≤ ‖edgeProfile b δ₁ k (lowHeightRoots γ₁ c Kset) x‖ ^ 2 *
      D ^ (3 + (3 * M - 4 * n - 11)) := by positivity
  rcases le_or_gt |ρ.im - γ₁| R with hnr | hfr
  · -- a near zero: its depth is at most `δ₁ + 1/(4b)`
    have hdep := hnear ρ hρ hnr
    have hexp : Real.exp (2 * |x.im| * b) ≤ Real.exp (2 * δ₁ * b + 1 / 2) := by
      apply Real.exp_le_exp.mpr
      rw [hxim]
      have : 2 * |ρ.re - 1 / 2| * b ≤ 2 * (δ₁ + 1 / (4 * b)) * b := by gcongr
      have e : 2 * (δ₁ + 1 / (4 * b)) * b = 2 * δ₁ * b + 1 / 2 := by field_simp; ring
      linarith
    have hDM : 1 ≤ D ^ M := one_le_pow₀ hD1
    calc ‖edgeProfile b δ₁ k (lowHeightRoots γ₁ c Kset) x‖ ^ 2 * D ^ (3 + (3 * M - 4 * n - 11))
        ≤ ‖edgeProfile b δ₁ k (lowHeightRoots γ₁ c Kset) x‖ ^ 2 * D ^ (3 + (3 * M - 4 * n - 11)) *
            D ^ M := le_mul_of_one_le_right hF0 hDM
      _ ≤ Real.exp (2 * |x.im| * b) * T := hΨ'
      _ ≤ Real.exp (2 * δ₁ * b + 1 / 2) * T := mul_le_mul_of_nonneg_right hexp hT0
      _ = _ := by rw [hTdef]; ring
  · -- a far zero: `D^M ≥ (1 + R)^M ≥ e^b`
    have hDR : (1 + R) ^ M ≤ D ^ M := pow_le_pow_left₀ (by linarith) (by rw [hD]; linarith) M
    have hexp : Real.exp (2 * |x.im| * b) ≤ Real.exp b :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hRpos : 0 < (1 + R) ^ M := by positivity
    have h1 : ‖edgeProfile b δ₁ k (lowHeightRoots γ₁ c Kset) x‖ ^ 2 *
        D ^ (3 + (3 * M - 4 * n - 11)) * (1 + R) ^ M ≤ (1 + R) ^ M * T := by
      calc _ ≤ ‖edgeProfile b δ₁ k (lowHeightRoots γ₁ c Kset) x‖ ^ 2 *
            D ^ (3 + (3 * M - 4 * n - 11)) * D ^ M := mul_le_mul_of_nonneg_left hDR hF0
        _ ≤ Real.exp (2 * |x.im| * b) * T := hΨ'
        _ ≤ Real.exp b * T := mul_le_mul_of_nonneg_right hexp hT0
        _ ≤ (1 + R) ^ M * T := mul_le_mul_of_nonneg_right hRM hT0
    have h2 : ‖edgeProfile b δ₁ k (lowHeightRoots γ₁ c Kset) x‖ ^ 2 *
        D ^ (3 + (3 * M - 4 * n - 11)) ≤ T := by
      rw [mul_comm ((1 + R) ^ M) T] at h1
      exact le_of_mul_le_mul_right h1 hRpos
    have hδ₁0 : 0 ≤ δ₁ := by linarith [hc.1, hc.2]
    have hex1 : 1 ≤ Real.exp (2 * δ₁ * b + 1 / 2) := Real.one_le_exp (by positivity)
    calc _ ≤ T := h2
      _ ≤ Real.exp (2 * δ₁ * b + 1 / 2) * T := le_mul_of_one_le_left hT0 hex1
      _ = _ := by rw [hTdef]; ring


/-! ### The final comparison -/

/-- The `L²` side of the relaxed criterion, in real variables. -/
theorem relaxed_L2_arith {Eθ I2 a b X Y G2 Q P : ℝ} (hEθ : 0 < Eθ)
    (hX : 0 < X) (hG2 : 0 ≤ G2)
    (hI2 : I2 ≤ 2 * a * (X * b ^ 10 * G2 * Q ^ 2))
    (hA : 512 * a * b ^ 6 * Real.exp 4 * Q ^ 2 * Eθ ≤ X)
    (hP : b ^ 4 * (X * X) * (Y * Y) / 256 ≤ P ^ 2) (hY : 1 ≤ Real.exp 4 * (Y * Y)) :
    Eθ * I2 ≤ P ^ 2 * G2 := by
  have hE4 : 0 < Real.exp 4 := Real.exp_pos 4
  have h1 : Eθ * I2 ≤ Eθ * (2 * a * (X * b ^ 10 * G2 * Q ^ 2)) :=
    mul_le_mul_of_nonneg_left hI2 hEθ.le
  have h2 : Eθ * (2 * a * (X * b ^ 10 * G2 * Q ^ 2)) =
      (512 * a * b ^ 6 * Real.exp 4 * Q ^ 2 * Eθ) * (b ^ 4 * X * G2 / (256 * Real.exp 4)) := by
    field_simp; ring
  have h3 : (512 * a * b ^ 6 * Real.exp 4 * Q ^ 2 * Eθ) * (b ^ 4 * X * G2 / (256 * Real.exp 4)) ≤
      X * (b ^ 4 * X * G2 / (256 * Real.exp 4)) :=
    mul_le_mul_of_nonneg_right hA (by positivity)
  have h4 : X * (b ^ 4 * X * G2 / (256 * Real.exp 4)) ≤ b ^ 4 * (X * X) * (Y * Y) / 256 * G2 := by
    have hinv : 1 / Real.exp 4 ≤ Y * Y := by rw [div_le_iff₀ hE4]; linarith
    calc X * (b ^ 4 * X * G2 / (256 * Real.exp 4))
        = b ^ 4 * (X * X) / 256 * G2 * (1 / Real.exp 4) := by field_simp
      _ ≤ b ^ 4 * (X * X) / 256 * G2 * (Y * Y) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = b ^ 4 * (X * X) * (Y * Y) / 256 * G2 := by ring
  have h5 : b ^ 4 * (X * X) * (Y * Y) / 256 * G2 ≤ P ^ 2 * G2 := mul_le_mul_of_nonneg_right hP hG2
  linarith

/-- The tail side of the relaxed criterion, in real variables. -/
theorem relaxed_tail_arith {T X Y b K D F G2 P : ℝ} (hX : 0 < X) (hD : 0 < D)
    (hG2 : 0 ≤ G2)
    (hT : T ≤ X * X * Real.exp (1 / 2) * 46656 * b ^ 12 * K / D)
    (hB : Real.exp (9 / 2) * 46656 * 256 * b ^ 8 * K < D * F) (hFG : F ≤ G2)
    (hP : b ^ 4 * (X * X) * (Y * Y) / 256 ≤ P ^ 2) (hY : 1 ≤ Real.exp 4 * (Y * Y))
    (hb1 : 1 ≤ b) : T < P ^ 2 * G2 := by
  have hE4 : 0 < Real.exp 4 := Real.exp_pos 4
  have hE9 : Real.exp (9 / 2) = Real.exp (1 / 2) * Real.exp 4 := by
    rw [← Real.exp_add]; norm_num
  have hb4 : 0 < b ^ 4 := by positivity
  refine lt_of_le_of_lt hT ?_
  rw [div_lt_iff₀ hD]
  have hXX : 0 < X * X := by positivity
  have hc : 0 < X * X * b ^ 4 / (256 * Real.exp 4) := by positivity
  calc X * X * Real.exp (1 / 2) * 46656 * b ^ 12 * K
      = X * X * b ^ 4 / (256 * Real.exp 4) * (Real.exp (9 / 2) * 46656 * 256 * b ^ 8 * K) := by
        rw [hE9]; field_simp
    _ < X * X * b ^ 4 / (256 * Real.exp 4) * (D * F) := mul_lt_mul_of_pos_left hB hc
    _ ≤ X * X * b ^ 4 / (256 * Real.exp 4) * (D * G2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFG hD.le) hc.le
    _ ≤ b ^ 4 * (X * X) * (Y * Y) / 256 * G2 * D := by
        have hinv : 1 / Real.exp 4 ≤ Y * Y := by rw [div_le_iff₀ hE4]; linarith
        calc X * X * b ^ 4 / (256 * Real.exp 4) * (D * G2)
            = b ^ 4 * (X * X) / 256 * (G2 * D) * (1 / Real.exp 4) := by field_simp
          _ ≤ b ^ 4 * (X * X) / 256 * (G2 * D) * (Y * Y) := by
              have : 0 ≤ G2 * D := mul_nonneg hG2 hD.le
              exact mul_le_mul_of_nonneg_left hinv (by positivity)
          _ = b ^ 4 * (X * X) * (Y * Y) / 256 * G2 * D := by ring
    _ ≤ P ^ 2 * G2 * D := by
        have : 0 ≤ G2 * D := mul_nonneg hG2 hD.le
        nlinarith

theorem relaxed_L2_bound {a b δ₁ : ℝ} {M : ℕ} (hb : 0 ≤ b) (hδ₁ : 0 ≤ δ₁)
    (hbM : b + M ≤ a) {I2 g Gn Q : ℝ} (hg0 : 0 ≤ g)
    (hL2 : I2 ≤ 2 * (b + M) * (Real.cosh (δ₁ * b) * b ^ 5 * g) ^ 2) (hg : g ≤ Gn * Q) :
    I2 ≤ 2 * a * (Real.exp (2 * δ₁ * b) * b ^ 10 * Gn ^ 2 * Q ^ 2) := by
  have hcosh := cosh_le_exp_self_of_nonneg (show 0 ≤ δ₁ * b by positivity)
  have h1 : Real.cosh (δ₁ * b) * b ^ 5 * g ≤ Real.exp (δ₁ * b) * b ^ 5 * (Gn * Q) := by
    have := Real.cosh_pos (δ₁ * b)
    gcongr
  have h1' : 0 ≤ Real.cosh (δ₁ * b) * b ^ 5 * g := by have := Real.cosh_pos (δ₁ * b); positivity
  have h2 := pow_le_pow_left₀ h1' h1 2
  have h3 : (Real.exp (δ₁ * b) * b ^ 5 * (Gn * Q)) ^ 2 =
      Real.exp (2 * δ₁ * b) * b ^ 10 * Gn ^ 2 * Q ^ 2 := by
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul]; ring_nf
  rw [h3] at h2
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  calc I2 ≤ 2 * (b + M) * (Real.cosh (δ₁ * b) * b ^ 5 * g) ^ 2 := hL2
    _ ≤ 2 * a * (Real.cosh (δ₁ * b) * b ^ 5 * g) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ ≤ 2 * a * (Real.exp (2 * δ₁ * b) * b ^ 10 * Gn ^ 2 * Q ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)

theorem relaxed_tail_le {b δ₁ γ₁ γs A₀ : ℝ} {M n : ℕ} (hb1 : 1 ≤ b) (hδ₁ : 0 < δ₁)
    (hδ₁2 : δ₁ ≤ 1 / 2) (hγ : |γ₁| ≤ |γs| + 1) (hA₀ : 1 ≤ A₀) :
    Real.exp (2 * δ₁ * b + 1 / 2) * (4 * testNorm (sinhTest b δ₁)) ^ 2 *
        clusterTailConstant 100 |γ₁| M n / (1 + 100) ^ (3 * M - 4 * n - 11) *
        (24 * A₀ * Real.log (|γ₁| + 3)) ≤
      Real.exp (2 * δ₁ * b) * Real.exp (2 * δ₁ * b) * Real.exp (1 / 2) * 46656 * b ^ 12 *
        ((Real.exp (1 / 2) * 168) ^ (2 * M) * 101 ^ (4 * n + 4) * (|γs| + 2) ^ 4 *
          (24 * A₀ * Real.log (|γs| + 4))) / (101 : ℝ) ^ (3 * M - 4 * n - 11) := by
  have htn := four_testNorm_sinhTest_sq_le hb1 hδ₁.le hδ₁2
  have hCG : clusterTailConstant 100 |γ₁| M n ≤
      (Real.exp (1 / 2) * 168) ^ (2 * M) * 101 ^ (4 * n + 4) * (|γs| + 2) ^ 4 := by
    unfold clusterTailConstant
    rw [show (100 : ℝ) + 1 = 101 by norm_num]
    have : |γ₁| + 1 ≤ |γs| + 2 := by linarith
    gcongr
  have hCG0 : 0 ≤ clusterTailConstant 100 |γ₁| M n := by unfold clusterTailConstant; positivity
  have hlog : Real.log (|γ₁| + 3) ≤ Real.log (|γs| + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (|γ₁| + 3) := Real.log_nonneg (by linarith [abs_nonneg γ₁])
  have hex : Real.exp (2 * δ₁ * b + 1 / 2) = Real.exp (2 * δ₁ * b) * Real.exp (1 / 2) := by
    rw [← Real.exp_add]
  have hD : (0 : ℝ) < 101 ^ (3 * M - 4 * n - 11) := by positivity
  rw [show (1 + 100 : ℝ) = 101 by norm_num, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hD.le
  rw [hex]
  have hA0 : (0 : ℝ) ≤ 24 * A₀ := by linarith
  have ht0 : 0 ≤ (4 * testNorm (sinhTest b δ₁)) ^ 2 := sq_nonneg _
  calc Real.exp (2 * δ₁ * b) * Real.exp (1 / 2) * (4 * testNorm (sinhTest b δ₁)) ^ 2 *
        clusterTailConstant 100 |γ₁| M n * (24 * A₀ * Real.log (|γ₁| + 3))
      ≤ Real.exp (2 * δ₁ * b) * Real.exp (1 / 2) * (46656 * b ^ 12 * Real.exp (2 * δ₁ * b)) *
          ((Real.exp (1 / 2) * 168) ^ (2 * M) * 101 ^ (4 * n + 4) * (|γs| + 2) ^ 4) *
          (24 * A₀ * Real.log (|γs| + 4)) := by
        gcongr
    _ = _ := by ring

theorem relaxed_floor_le {δ b δ₁ η G2 : ℝ} {M n : ℕ} (hδ : 0 < δ) (hb : 0 < b)
    (hηlow : relaxedKillScale δ b M n ≤ η) (hδ₁ : δ / 2 ≤ δ₁)
    (h : unitWeightFloor ^ (2 * M) * η ^ (4 * n) * δ₁ ^ 4 ≤ G2) :
    unitWeightFloor ^ (2 * M) * relaxedKillScale δ b M n ^ (4 * n) * (δ / 2) ^ 4 ≤ G2 := by
  refine le_trans ?_ h
  have hk0 := relaxedKillScale_pos hδ hb M n
  have := unitWeightFloor_pos
  have hη0 : 0 ≤ η := le_trans hk0.le hηlow
  gcongr

/-! ### The core relaxed criterion -/

/-- **Core relaxed criterion.**  Let `ρs = ½ + δ + iγs` be a zero such that every zero within
ordinate `R + 1` of it has depth `≤ δ + 1/(8b)`, and at most `n` zeros satisfy `|γ - γs| ≤ 101`.
If `4 ≤ b`, `b + M ≤ a`, `e^b ≤ (1 + R)^M`, `2n + 7 ≤ M`, `δ(b - 2) ≥ 1`, and the two size
conditions `hA`, `hB` hold, then the relaxed Hodge index with exponent `θ` fails at level `a`. -/
theorem relaxed_test_package (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hlow : ∀ ρ ∈ Z.carrier, 2 ≤ |ρ.im|)
    {ρs : ℂ} (hρs : ρs ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρs.re = 1 / 2 + δ)
    {a b R : ℝ} {M n : ℕ} (hb4 : 4 ≤ b) (hbM : b + M ≤ a) (hR : 0 ≤ R)
    (hRM : Real.exp b ≤ (1 + R) ^ M)
    (hdepth : ∀ ρ ∈ Z.carrier, |ρ.im - ρs.im| ≤ R + 1 → |ρ.re - 1 / 2| ≤ δ + 1 / (8 * b))
    (hn : (Z.finite_window (ρs.im - (100 + 1)) (ρs.im + (100 + 1))).toFinset.card ≤ n)
    (hM : 2 * n + 7 ≤ M) (hδb : 1 ≤ δ * (b - 2))
    :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
      paperFT f (-(I / 2)) = 0 ∧ ∃ δ₁ γ₁ η P G2 : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 / 2 ∧
        δ - 1 / (8 * b) ≤ δ₁ ∧ δ / 2 ≤ δ₁ ∧ |γ₁| ≤ |ρs.im| + 1 ∧
        relaxedKillScale δ b M n ≤ η ∧ 0 ≤ G2 ∧
        (Z.W f f).re ≤ -2 * (P ^ 2 * G2) +
          Real.exp (2 * δ₁ * b + 1 / 2) * (4 * testNorm (sinhTest b δ₁)) ^ 2 *
            clusterTailConstant 100 |γ₁| M n / (1 + 100) ^ (3 * M - 4 * n - 11) *
            (24 * A₀ * Real.log (|γ₁| + 3)) ∧
        ∫ u, ‖f u‖ ^ 2 ≤
          2 * a * (Real.exp (2 * δ₁ * b) * b ^ 10 * G2 * relaxedRootRatio δ b M n ^ 2) ∧
        b ^ 4 * (Real.exp (2 * δ₁ * b) * Real.exp (2 * δ₁ * b)) *
          (Real.exp (-(4 * δ₁)) * Real.exp (-(4 * δ₁))) / 256 ≤ P ^ 2 ∧
        unitWeightFloor ^ (2 * M) * η ^ (4 * n) * δ₁ ^ 4 ≤ G2 := by
  classical
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hst := Z.strip ρs hρs
  have hδ2 : δ ≤ 1 / 2 := by linarith [hst.2]
  -- the halving radius
  set r₀ := min (lowHeightEps0 δ M) (1 / (10 ^ 5 * b ^ 5)) with hr₀def
  have hr₀ : 0 < r₀ := lt_min (lowHeightEps0_pos hδ M) (by positivity)
  have hr₀s : r₀ ≤ lowHeightEps0 δ M := min_le_left _ _
  have hr₀b : r₀ ≤ 1 / (10 ^ 5 * b ^ 5) := min_le_right _ _
  have hb5 : 1 ≤ b ^ 5 := one_le_pow₀ hb1
  have hr₀8 : r₀ ≤ 1 / (8 * b) := by
    refine hr₀b.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [pow_le_pow_right₀ hb1 (show 1 ≤ 5 by norm_num)]
  have hr₀1 : r₀ ≤ 1 := hr₀s.trans (lowHeightEps0_le hδ M).2 |>.trans (by norm_num)
  obtain ⟨ρ₁, hρ₁, δ₁, hre₁, hδ₁half, hδδ₁, hγ₁, Kset, hKW, hKn, ε, η, hε0, hεε, hεr₀, hη1,
    hηlow, hεη, hclu, hkil⟩ :=
    cluster_selection_radius (N₀ := M) Z hρs hδ hre (H := 100) (by norm_num) hn hr₀ hr₀s
  set γ₁ := ρ₁.im with hγ₁def
  have hst₁ := Z.strip ρ₁ hρ₁
  have hδ₁0 : 0 < δ₁ := by linarith
  have hδ₁2 : δ₁ ≤ 1 / 2 := by linarith [hst₁.2]
  have hδ₁lo : δ - 1 / (8 * b) ≤ δ₁ := by linarith [(abs_lt.mp hδδ₁).2]
  have hγ₁1 : 1 ≤ |γ₁| := by
    have h2 := hlow ρs hρs
    have := abs_sub_abs_le_abs_sub ρs.im γ₁
    rw [abs_sub_comm] at hγ₁
    linarith
  have hγ₁s : |γ₁| ≤ |ρs.im| + 1 := by
    have := abs_sub_abs_le_abs_sub γ₁ ρs.im
    linarith
  have hδ₁b : 1 / 2 ≤ δ₁ * (b - 2) := by nlinarith
  have hη0 : 0 < η := lt_of_lt_of_le (by
    have := hr₀; unfold lowHeightScale; positivity) hηlow
  have hε1 : ε ≤ 1 := hεr₀.trans hr₀1
  have hεb : ε * (10 ^ 5 * b ^ 5) ≤ 1 := by
    have := hεr₀.trans hr₀b
    rwa [le_div_iff₀ (by positivity)] at this
  have hWn : ∀ ρ, ρ ∈ (Z.finite_window (γ₁ - 100) (γ₁ + 100)).toFinset ↔
      ρ ∈ Z.carrier ∧ γ₁ - 100 < ρ.im ∧ ρ.im ≤ γ₁ + 100 := by
    intro ρ; rw [Set.Finite.mem_toFinset]; rfl
  have hKH : ∀ σ ∈ Kset, σ ∈ Z.carrier ∧ |σ.im - γ₁| ≤ 100 := by
    intro σ hσ
    obtain ⟨hσZ, h1, h2⟩ := (hWn σ).mp (hKW hσ)
    exact ⟨hσZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hS : (M : ℝ) * (4 * ε) + (2 * (n : ℝ)) * (ε / η) + 2 * ε + 2 * ε / δ₁ ≤ 1 / 20 := by
    rw [hεη]; exact lowHeight_scale_bound hδ₁0 hε0.le hεε
  -- the phase root makes `G(x₁)` real
  obtain ⟨c, hc, hcre⟩ := exists_phase_rotation hδ₁0
    (I * (paperFT (fun u => (sinhTestWeight 1 u : ℂ)) (-(I * δ₁)) ^
        (M - (2 * (Kset.card + 2) + 1) + 2 * (Kset.card + 2) + 1) *
      ((Kset.toList.map (fun ρ => gammaOf ρ - γ₁) ++ [(⟨-γ₁, 1 / 2⟩ : ℂ)]).map
        (fun r => (-(I * δ₁) - r) * (-(I * δ₁) - conj r))).prod))
  set k := M - (2 * (Kset.card + 2) + 1) with hkdef
  set L := lowHeightRoots γ₁ c Kset with hL
  have hLlen := lowHeightRoots_length γ₁ c Kset
  have hk : k + 2 * L.length + 1 = M := by rw [hL, hLlen]; omega
  set G₁ := lowHeightProfile (sinhTestWeight 1) k L (-(I * δ₁)) with hG₁
  have hG₁im : G₁.im = 0 := by
    have h := lowHeightProfile_x₀_eq k γ₁ c δ₁ Kset
    rw [← hL, hLlen] at h
    rw [hG₁, h]
    have e : ((c : ℂ) + I * δ₁) ^ 2 * (I * (paperFT (fun u => (sinhTestWeight 1 u : ℂ)) (-(I * δ₁)) ^
        (M - (2 * (Kset.card + 2) + 1) + 2 * (Kset.card + 2) + 1) *
      ((Kset.toList.map (fun ρ => gammaOf ρ - γ₁) ++ [(⟨-γ₁, 1 / 2⟩ : ℂ)]).map
        (fun r => (-(I * δ₁) - r) * (-(I * δ₁) - conj r))).prod)) =
        I * (paperFT (fun u => (sinhTestWeight 1 u : ℂ)) (-(I * δ₁)) ^
        (k + 2 * (Kset.card + 2) + 1) *
      ((Kset.toList.map (fun ρ => gammaOf ρ - γ₁) ++ [(⟨-γ₁, 1 / 2⟩ : ℂ)]).map
        (fun r => (-(I * δ₁) - r) * (-(I * δ₁) - conj r))).prod * ((c : ℂ) + I * δ₁) ^ 2) := by
      rw [hkdef]; ring
    rw [e, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at hcre
    linarith
  -- the test
  set f := edgeTest γ₁ b δ₁ k L with hf
  obtain ⟨hfc, hfs, hff⟩ := edgeTest_props (γ := γ₁) hb0.le δ₁ k L
  have hLM : ((k + 2 * L.length + 1 : ℕ) : ℝ) = M := by exact_mod_cast hk
  have hfsupp : tsupport f ⊆ Icc (-a) a := by
    refine tsupport_subset_of_support_subset_abs fun u hu => ?_
    have := hfs u hu
    rw [hLM] at this
    linarith
  have hpolar : edgeProfile b δ₁ k L (I / 2 - γ₁) = 0 := by
    have : I / 2 - (γ₁ : ℂ) = (⟨-γ₁, 1 / 2⟩ : ℂ) := by apply Complex.ext <;> simp
    rw [this]
    have hG0 : lowHeightProfile (sinhTestWeight 1) k L (⟨-γ₁, 1 / 2⟩ : ℂ) = 0 :=
      lowHeightProfile_eq_zero_of_mem (by rw [hL]; unfold lowHeightRoots; simp)
    rw [edgeProfile, hG0, mul_zero]
  have hpolar' : edgeProfile b δ₁ k L (-(I / 2) - γ₁) = 0 := by
    have : -(I / 2) - (γ₁ : ℂ) = conj (⟨-γ₁, 1 / 2⟩ : ℂ) := by apply Complex.ext <;> simp
    rw [this]
    have hG0 : lowHeightProfile (sinhTestWeight 1) k L (conj (⟨-γ₁, 1 / 2⟩ : ℂ)) = 0 :=
      lowHeightProfile_eq_zero_of_conj_mem (by rw [hL]; unfold lowHeightRoots; simp)
    rw [edgeProfile, hG0, mul_zero]
  have hp : paperFT f (I / 2) = 0 := by rw [hff, hpolar, mul_zero]
  have hm : paperFT f (-(I / 2)) = 0 := by rw [hff, hpolar', mul_zero]
  -- the value at the deep zero
  set P := ∫ u, sinhTest b δ₁ u * Real.sinh (δ₁ * u) with hPdef
  have hPlow := sinhTest_energy_ge_exp hb4 hδ₁0 hδ₁b
  have hP0 : 0 ≤ P := le_trans (by positivity) hPlow
  have hΨ₁ : edgeProfile b δ₁ k L (-(I * δ₁)) = I * (P : ℂ) * G₁ :=
    edgeProfile_neg_I_mul b δ₁ hb0.le k L
  have hΨ₁re : (edgeProfile b δ₁ k L (-(I * δ₁))).re = 0 := by
    rw [hΨ₁]; simp [Complex.mul_re, hG₁im]
  have hsq := sq_eq_neg_normSq_of_re_eq_zero hΨ₁re
  have hΨ₁n : ‖edgeProfile b δ₁ k L (-(I * δ₁))‖ ^ 2 = P ^ 2 * ‖G₁‖ ^ 2 := by
    rw [hΨ₁, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hP0]; ring
  -- the Weil form
  have hwin := edge_window_nonpos (c := c) (Wn := (Z.finite_window (γ₁ - 100) (γ₁ + 100)).toFinset)
    hδ₁0 hδ₁2 hγ₁1 hb4 hδ₁b hKn hε0 hε1 hεb hη0 hclu hkil hS hk hsq
  have hnear : ∀ ρ ∈ Z.carrier, |ρ.im - γ₁| ≤ R → |ρ.re - 1 / 2| ≤ δ₁ + 1 / (4 * b) := by
    intro ρ hρ hρR
    have h1 : |ρ.im - ρs.im| ≤ R + 1 := by
      have := abs_sub_le ρ.im γ₁ ρs.im
      linarith
    have h2 := hdepth ρ hρ h1
    have e : 1 / (4 * b) = 1 / (8 * b) + 1 / (8 * b) := by field_simp; ring
    linarith
  have htail := edge_tail_bound Z hb0 hc hδ₁2 hKH hk hKn hM hR hRM hnear
  set C₁ := Real.exp (2 * δ₁ * b + 1 / 2) * (4 * testNorm (sinhTest b δ₁)) ^ 2 *
    clusterTailConstant 100 |γ₁| M n with hC₁def
  have hCG0 : 0 ≤ clusterTailConstant 100 |γ₁| M n := by unfold clusterTailConstant; positivity
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hW := re_W_le_of_profile Z hA₀ hloc (f := f) (Ψ := edgeProfile b δ₁ k L) (γ₁ := γ₁)
    (fun ρ => Wsummand_edgeTest Z hb0.le δ₁ k L ρ) (edgeProfile_conj b δ₁ k L)
    hρ₁ hδ₁0 hre₁ rfl (by norm_num : (0 : ℝ) < 100) hWn hwin hsq (E := 3 * M - 4 * n - 11) hC₁0
    (fun ρ hρ _ => htail ρ hρ)
  -- the `L²` norm
  have hr' : ∀ r ∈ pairRoots L, -(I * (δ₁ : ℂ)) - r ≠ 0 :=
    ne_of_pairRoots_lowHeightRoots (c := c) hδ₁0 hη0 hγ₁1 hkil
  have hL1 := integral_norm_edgeKill_le_ratio δ₁ k L hr'
  have hQ := rootRatio_lowHeightRoots_le Z hδ₁0 hη0 hη1 hγ₁1 hc hδ₁2 hKH hKn hkil
  have hQhi : (122 / η) ^ (2 * n) * (495 / δ₁) ^ 2 ≤ relaxedRootRatio δ b M n := by
    unfold relaxedRootRatio
    have hk0 := relaxedKillScale_pos hδ hb0 M n
    have hηk : relaxedKillScale δ b M n ≤ η := hηlow
    have h1 : (122 / η) ^ (2 * n) ≤ (122 / relaxedKillScale δ b M n) ^ (2 * n) := by
      gcongr
    have h2 : (495 / δ₁) ^ 2 ≤ (990 / δ) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_div_iff₀ hδ₁0 hδ]; linarith
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hQ0 : 0 ≤ ((pairRoots L).map fun r =>
      (unitDerivL1 + ‖r‖ * unitL1) / (unitL1 * ‖-(I * (δ₁ : ℂ)) - r‖)).prod :=
    List.prod_nonneg fun y hy => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hy
      have := unitDerivL1_nonneg; have := unitL1_pos; positivity
  have hg1 : ∫ u, ‖edgeKill k L u‖ ≤ ‖G₁‖ * relaxedRootRatio δ b M n :=
    hL1.trans (mul_le_mul_of_nonneg_left (hQ.trans hQhi) (norm_nonneg _))
  have hgn : 0 ≤ ∫ u, ‖edgeKill k L u‖ := integral_nonneg fun _ => norm_nonneg _
  have hL2 := integral_norm_sq_edgeTest_le (γ := γ₁) hb0.le hδ₁0.le k L
  rw [hLM] at hL2
  -- the package
  have hPsq : b ^ 4 * (Real.exp (2 * δ₁ * b) * Real.exp (2 * δ₁ * b)) *
      (Real.exp (-(4 * δ₁)) * Real.exp (-(4 * δ₁))) / 256 ≤ P ^ 2 := by
    have he : Real.exp (2 * (δ₁ * (b - 2))) = Real.exp (2 * δ₁ * b) * Real.exp (-(4 * δ₁)) := by
      rw [← Real.exp_add]; ring_nf
    rw [he] at hPlow
    have h0 : 0 ≤ b ^ 2 * (Real.exp (2 * δ₁ * b) * Real.exp (-(4 * δ₁))) / 16 := by positivity
    have := pow_le_pow_left₀ h0 hPlow 2
    calc _ = (b ^ 2 * (Real.exp (2 * δ₁ * b) * Real.exp (-(4 * δ₁))) / 16) ^ 2 := by ring
      _ ≤ P ^ 2 := this
  have hL2' := relaxed_L2_bound hb0.le hδ₁0.le hbM hgn hL2 hg1
  refine ⟨f, hfc, hfsupp, hp, hm, δ₁, γ₁, η, P, ‖G₁‖ ^ 2, hδ₁0, hδ₁2, hδ₁lo, hδ₁half, hγ₁s,
    hηlow, sq_nonneg _, ?_, hL2', hPsq,
    norm_sq_lowHeightProfile_x₀_ge (c := c) hδ₁0 hγ₁1 hη0 hη1 hKn hkil hk⟩
  rw [hΨ₁n] at hW
  exact hW

/-- **Core relaxed criterion.**  Let `ρs = ½ + δ + iγs` be a zero such that every zero within
ordinate `R + 1` of it has depth `≤ δ + 1/(8b)`, and at most `n` zeros satisfy `|γ - γs| ≤ 101`.
If `4 ≤ b`, `b + M ≤ a`, `e^b ≤ (1 + R)^M`, `2n + 7 ≤ M`, `δ(b - 2) ≥ 1`, and the two size
conditions `hA`, `hB` hold, then the relaxed Hodge index with exponent `θ` fails at level `a`. -/
theorem exists_relaxed_violation (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hlow : ∀ ρ ∈ Z.carrier, 2 ≤ |ρ.im|)
    {ρs : ℂ} (hρs : ρs ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρs.re = 1 / 2 + δ)
    {θ a b R : ℝ} {M n : ℕ} (hb4 : 4 ≤ b) (hbM : b + M ≤ a) (hR : 0 ≤ R)
    (hRM : Real.exp b ≤ (1 + R) ^ M)
    (hdepth : ∀ ρ ∈ Z.carrier, |ρ.im - ρs.im| ≤ R + 1 → |ρ.re - 1 / 2| ≤ δ + 1 / (8 * b))
    (hn : (Z.finite_window (ρs.im - (100 + 1)) (ρs.im + (100 + 1))).toFinset.card ≤ n)
    (hM : 2 * n + 7 ≤ M) (hδb : 1 ≤ δ * (b - 2))
    (hA : 512 * a * b ^ 6 * Real.exp 4 * relaxedRootRatio δ b M n ^ 2 * Real.exp (θ * a) ≤
      Real.exp (2 * (δ - 1 / (8 * b)) * b))
    (hB : Real.exp (9 / 2) * 46656 * 256 * b ^ 8 * ((Real.exp (1 / 2) * 168) ^ (2 * M) *
        101 ^ (4 * n + 4) * (|ρs.im| + 2) ^ 4 * (24 * A₀ * Real.log (|ρs.im| + 4))) <
      (101 : ℝ) ^ (3 * M - 4 * n - 11) * (unitWeightFloor ^ (2 * M) *
        relaxedKillScale δ b M n ^ (4 * n) * (δ / 2) ^ 4)) :
    ¬ RelaxedHodgeIndexAtLevel Z θ a := by
  intro hrel
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  obtain ⟨f, hfc, hfsupp, hp, hm, δ₁, γ₁, η, P, G2, hδ₁0, hδ₁2, hδ₁lo, hδ₁half, hγ₁s, hηlow,
    hG20, hW, hL2, hPsq, hfloor⟩ :=
    relaxed_test_package Z hA₀ hloc hlow hρs hδ hre hb4 hbM hR hRM hdepth hn hM hδb
  have hY2 : 1 ≤ Real.exp 4 * (Real.exp (-(4 * δ₁)) * Real.exp (-(4 * δ₁))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have hstep1 := relaxed_L2_arith (Real.exp_pos (θ * a)) (Real.exp_pos (2 * δ₁ * b)) hG20 hL2
    (hA.trans (Real.exp_le_exp.mpr (by nlinarith))) hPsq hY2
  have hstep2 := relaxed_tail_arith (Real.exp_pos (2 * δ₁ * b)) (by positivity) hG20
    (relaxed_tail_le hb1 hδ₁0 hδ₁2 hγ₁s hA₀) hB (relaxed_floor_le hδ hb0 hηlow hδ₁half hfloor)
    hPsq hY2 hb1
  have hrelf := hrel f hfc hfsupp hp hm
  linarith [hW, hstep1, hstep2, hrelf]

end RHTower
