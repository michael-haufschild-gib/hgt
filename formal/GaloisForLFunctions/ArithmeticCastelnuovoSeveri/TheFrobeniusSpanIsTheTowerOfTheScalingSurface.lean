import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurfaceOfACurve
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic

/-!
# The Frobenius span is the `q`-tower of the scaling surface of a curve

Weil's proof uses the Frobenius span `Γ_0, Γ_1, …` with the Toeplitz Gram matrix of the power sums
`Σ_i β_i^{|k−l|}`; ACS reads the same curve as the scaling surface of its zero configuration
`q^{ρ − ½} = β_i` (`curveConfig`). This file proves that the first is a literal piece of the
second, by an identity.

* **The explicit formula of a curve** (`W_curveConfig`). For compactly supported tests,
  Weil's form of the zero configuration is the lattice sum of `k = f ⋆ g̃`:

      W(f, g) = Σ_i log q · Σ_{m ∈ ℤ} k(m log q) β_i^m.

  The zeros attached to `β_i` form a tilted vertical lattice, and Poisson summation
  (`RHTower.hasSum_paperFT_lattice_sub_I_mul`) turns each lattice of transforms into the samples
  `k(m log q)` weighted by `β_i^m` (`hasSum_paperFT_zetaZero`); the multiplicity of a zero is the
  number of indices `i` mapping to it (`natCard_fiber`). The lag `m log q` carries the Lefschetz
  number: `q^{m/2} Σ_i β_i^m = q^m + 1 − N_m`.
* **The `q`-tower is the Frobenius span** (`curve_towerGram_eq_smul_spanGram`). For a test `g`
  supported in an interval shorter than `log q`, the translates `g(· − k log q)` — the Hecke tower at
  the prime power `q` — have Gram matrix exactly `log q · ‖g‖² · spanGram`: only the lag `k − l`
  survives, with weight `Σ_i β_i^{k−l} = Σ_i β_i^{|k−l|}` (`sum_zpow_eq_trace`). Hence the tower
  defect of the scaling surface equals the Frobenius span defect, the number of distinct eigenvalues
  outside the unit circle (`curve_tower_pontryagin_law`); for the golden fake curve it is `1`
  (`goldenDatum_tower_negIndex`).

So the statement "the Frobenius span is the scaling surface modulo the period" is an identity of
Gram matrices, and the tower Pontryagin law of `TheHeckeTowerOfAPrimeIsThePeriodQuotient` reduces
over `𝔽_q` to `pontryagin_law_curve`.
-/

open Complex Finset
open scoped Real ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Inertia under positive scaling -/

theorem hermQuad_ofReal_smul {n : Type*} [Fintype n] (c : ℝ) (H : Matrix n n ℂ) (x : n → ℂ) :
    hermQuad ((c : ℂ) • H) x = c * hermQuad H x := by
  simp only [hermQuad, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.re_ofReal_mul]

theorem hermPosIndex_ofReal_smul {n : Type*} [Fintype n] {c : ℝ} (hc : 0 < c)
    (H : Matrix n n ℂ) : hermPosIndex ((c : ℂ) • H) = hermPosIndex H := by
  have key : ∀ W, IsPosDefOn ((c : ℂ) • H) W ↔ IsPosDefOn H W := fun W => by
    simp only [IsPosDefOn, hermQuad_ofReal_smul]
    exact forall₂_congr fun x _ => imp_congr_right fun _ =>
      ⟨fun h => (mul_pos_iff_of_pos_left hc).mp h, fun h => mul_pos hc h⟩
  apply le_antisymm
  · obtain ⟨W, hW, hpd⟩ := exists_isPosDefOn_finrank_eq_posIndex ((c : ℂ) • H)
    rw [← hW]; exact finrank_le_posIndex ((key W).mp hpd)
  · obtain ⟨W, hW, hpd⟩ := exists_isPosDefOn_finrank_eq_posIndex H
    rw [← hW]; exact finrank_le_posIndex ((key W).mpr hpd)

/-- Scaling by a positive real does not change the negative index. -/
theorem hermNegIndex_ofReal_smul {n : Type*} [Fintype n] {c : ℝ} (hc : 0 < c)
    (H : Matrix n n ℂ) : hermNegIndex ((c : ℂ) • H) = hermNegIndex H := by
  unfold hermNegIndex
  rw [← smul_neg]
  exact hermPosIndex_ofReal_smul hc (-H)

/-! ### Transforms and translates -/

/-- Modulation shifts the transform: `h_{K e^{ixu}}(z) = h_K(z + x)`. -/
theorem paperFT_modulate (K : ℝ → ℂ) (x : ℝ) (z : ℂ) :
    paperFT (fun u => K u * cexp (I * x * u)) z = paperFT K (z + x) := by
  simp only [paperFT]
  congr 1
  funext u
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Translating both tests shifts their cross-correlation by the difference of the shifts. -/
theorem weilTest_translate (a b : ℝ) (f g : ℝ → ℂ) (u : ℝ) :
    EF.weilTest (translate a f) (translate b g) u = EF.weilTest f g (u - (a - b)) := by
  rw [RHTower.weilTest_apply, RHTower.weilTest_apply]
  simp only [translate]
  rw [← MeasureTheory.integral_add_right_eq_self (fun t => f (t - a) * conj (g (t - u - b))) a]
  congr 1
  funext s
  rw [add_sub_cancel_right]
  congr 3
  ring

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The zeros of `β_i` form the tilted lattice `γ = arg β_i/log q + 2πk/log q − i log|β_i|/log q`. -/
theorem gammaOf_zetaZero (i : ι) (k : ℤ) :
    gammaOf (D.zetaZero i k) =
      (((k : ℝ) * (2 * π / Real.log D.q) : ℝ) : ℂ) - I * ((Real.log ‖D.β i‖ / Real.log D.q : ℝ))
        + ((arg (D.β i) / Real.log D.q : ℝ) : ℂ) := by
  rw [gammaOf, div_eq_iff I_ne_zero]
  apply Complex.ext
  · simp [zetaZero, Complex.mul_re]
  · simp [zetaZero, Complex.mul_im, period]
    ring

/-- **Poisson summation along the zeros of one eigenvalue.** For a `C²` kernel of bounded
support, the transforms at the zeros `ρ_{i,k}`, `k ∈ ℤ`, sum to `log q · Σ_m K(m log q) β_i^m`. -/
theorem hasSum_paperFT_zetaZero (i : ι) {K : ℝ → ℂ} {A : ℝ} (hK : ContDiff ℝ 2 K)
    (hKs : ∀ u, K u ≠ 0 → |u| ≤ A) :
    HasSum (fun k : ℤ => paperFT K (gammaOf (D.zetaZero i k)))
      (Real.log D.q * ∑' m : ℤ, K (m * Real.log D.q) * D.β i ^ m) := by
  set L := Real.log D.q with hL
  have hL0 : L ≠ 0 := D.log_q_pos.ne'
  set x : ℝ := arg (D.β i) / L
  set δ : ℝ := Real.log ‖D.β i‖ / L
  set K' : ℝ → ℂ := fun u => K u * cexp (I * x * u) with hK'def
  have hK' : ContDiff ℝ 2 K' :=
    hK.mul (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))
  have hK's : ∀ u, K' u ≠ 0 → |u| ≤ A := fun u hu => hKs u fun h => hu (by simp [hK'def, h])
  have h := RHTower.hasSum_paperFT_lattice_sub_I_mul D.log_q_pos hK' hK's δ
  convert h using 1
  · funext k
    rw [gammaOf_zetaZero, hK'def, paperFT_modulate]
  · congr 1
    refine tsum_congr fun m => ?_
    simp only [hK'def]
    rw [mul_assoc]
    congr 1
    have hβ := D.β_ne_zero i
    have hL0' : (L : ℂ) ≠ 0 := by exact_mod_cast hL0
    have e1 : I * (x : ℂ) * ((m * L : ℝ) : ℂ) + ((δ * (m * L) : ℝ) : ℂ) =
        (m : ℂ) * Complex.log (D.β i) := by
      rw [Complex.log]
      simp only [x, δ]
      push_cast
      field_simp
      ring
    rw [Complex.ofReal_exp, ← Complex.exp_add, e1, Complex.exp_int_mul, Complex.exp_log hβ]

theorem zetaZero_injective_right (i : ι) : Function.Injective (D.zetaZero i) := by
  intro k k' h
  have him := congrArg Complex.im h
  simp only [im_zetaZero] at him
  have hp := D.period_pos
  exact_mod_cast mul_right_cancel₀ hp.ne' (by linarith : (k : ℝ) * D.period = k' * D.period)

variable (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-- The map `(i, k) ↦ ρ_{i,k}` onto the carrier. -/
def zeroIndex : ι × ℤ → (D.curveConfig hD).carrier := fun p => ⟨D.zetaZero p.1 p.2, p, rfl⟩

/-- The fibre of `(i, k) ↦ ρ_{i,k}` over a zero has `mult ρ` points. -/
theorem natCard_fiber (ρ : (D.curveConfig hD).carrier) :
    Nat.card (D.zeroIndex hD ⁻¹' {ρ}) = (D.curveConfig hD).mult ρ := by
  classical
  have hval : ∀ p : D.zeroIndex hD ⁻¹' {ρ}, D.zetaZero p.1.1 p.1.2 = ρ := fun p =>
    congrArg Subtype.val (Set.mem_singleton_iff.mp p.2)
  let F : D.zeroIndex hD ⁻¹' {ρ} →
      (univ.filter fun i => (D.q : ℂ) ^ ((ρ : ℂ) - 1 / 2) = D.β i) := fun p =>
    ⟨p.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hval p]; exact D.cpow_zetaZero _ _⟩⟩
  have hbij : Function.Bijective F := by
    constructor
    · rintro ⟨⟨i, k⟩, hk⟩ ⟨⟨i', k'⟩, hk'⟩ h
      have hi : i = i' := congrArg Subtype.val h
      subst hi
      have h1 := hval ⟨⟨i, k⟩, hk⟩
      have h2 := hval ⟨⟨i, k'⟩, hk'⟩
      have hkk : k = k' := D.zetaZero_injective_right i (h1.trans h2.symm)
      subst hkk
      rfl
    · rintro ⟨i, hi⟩
      obtain ⟨k, hk⟩ := D.exists_zetaZero_eq (Finset.mem_filter.mp hi).2
      exact ⟨⟨(i, k), Set.mem_singleton_iff.mpr (Subtype.ext hk)⟩, rfl⟩
  rw [Nat.card_eq_of_bijective F hbij, Nat.card_eq_fintype_card, Fintype.card_coe]
  simp [curveConfig]

/-- **The explicit formula of a curve.** For compactly supported tests, Weil's form of the zero
configuration is `Σ_i log q · Σ_{m ∈ ℤ} (f ⋆ g̃)(m log q) β_i^m`. -/
theorem W_curveConfig {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    (D.curveConfig hD).W f g =
      ∑ i, Real.log D.q * ∑' m : ℤ, EF.weilTest f g (m * Real.log D.q) * D.β i ^ m := by
  classical
  set L := Real.log D.q
  set K := EF.weilTest f g with hKdef
  have hK : ContDiff ℝ 2 K := EF.weilTest_contDiff hf hg hfc
  have hKc : HasCompactSupport K := EF.weilTest_hasCompactSupport hfc hgc
  obtain ⟨A, -, hA⟩ := GaloisForLFunctions.SquareRootThreshold.exists_radius_of_hasCompactSupport hKc
  have hKs : ∀ u, K u ≠ 0 → |u| ≤ A := fun u hu => not_lt.mp fun h => hu (hA u h)
  set F : ι × ℤ → ℂ := fun p => paperFT K (gammaOf (D.zetaZero p.1 p.2)) with hF
  have hFi : ∀ i, HasSum (fun p : ι × ℤ => if p.1 = i then F p else 0)
      (L * ∑' m : ℤ, K (m * L) * D.β i ^ m) := by
    intro i
    have hinj : Function.Injective (fun k : ℤ => (i, k)) := fun k k' h => (Prod.mk.inj h).2
    have h0 : ∀ p ∉ Set.range (fun k : ℤ => (i, k)), (if p.1 = i then F p else 0) = 0 := by
      intro p hp
      rw [if_neg]
      intro hpi
      exact hp ⟨p.2, Prod.ext hpi.symm rfl⟩
    rw [← hinj.hasSum_iff h0]
    simpa [Function.comp_def, hF] using D.hasSum_paperFT_zetaZero i hK hKs
  have hFsum : HasSum F (∑ i, L * ∑' m : ℤ, K (m * L) * D.β i ^ m) := by
    have h := hasSum_sum (s := Finset.univ) fun i _ => hFi i
    convert h using 1
    funext p
    rw [Finset.sum_ite_eq]
    simp
  have hfib := hFsum.tsum_fiberwise (D.zeroIndex hD)
  have hW : ∀ ρ : (D.curveConfig hD).carrier, (D.curveConfig hD).Wsummand f g ρ =
      ∑' b : D.zeroIndex hD ⁻¹' {ρ}, F b := by
    intro ρ
    have hconst : ∀ b : D.zeroIndex hD ⁻¹' {ρ}, F b = paperFT K (gammaOf ρ) := fun b => by
      simp only [hF]
      rw [show D.zetaZero b.1.1 b.1.2 = ρ from
        congrArg Subtype.val (Set.mem_singleton_iff.mp b.2)]
    rw [tsum_congr hconst, tsum_const, D.natCard_fiber hD ρ, nsmul_eq_mul, ZeroConfig.Wsummand,
      hKdef, EF.paperFT_weilTest hf.continuous hg hfc hgc, mul_assoc]
  rw [ZeroConfig.W, tsum_congr hW]
  exact hfib.tsum_eq

/-- `Σ_i β_i^m = Σ_i β_i^{|m|}`, the trace at lag `|m|`: the spectrum is closed under `β ↦ 1/β`. -/
theorem sum_zpow_eq_trace (m : ℤ) : ∑ i, D.β i ^ m = (D.trace m.natAbs : ℂ) := by
  rw [← D.powerSum_eq_trace, powerSum]
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · simp [zpow_natCast]
  · rw [Int.natAbs_neg, Int.natAbs_natCast]
    simp only [zpow_neg, zpow_natCast]
    rw [← Equiv.sum_comp D.fePerm (fun i => D.β i ^ n)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eq_inv_of_mul_eq_one_left (D.β_fePerm i), inv_pow]

theorem natAbs_sub_eq_dist (k l : ℕ) : ((k : ℤ) - l).natAbs = Nat.dist k l := by
  rcases le_total k l with h | h
  · rw [Nat.dist_eq_sub_of_le h, show (k : ℤ) - l = -((l - k : ℕ) : ℤ) by push_cast [h]; ring,
      Int.natAbs_neg, Int.natAbs_natCast]
  · rw [Nat.dist_eq_sub_of_le_right h, show (k : ℤ) - l = ((k - l : ℕ) : ℤ) by push_cast [h]; ring,
      Int.natAbs_natCast]

/-- **Narrow translates along the tower.** For `g` supported in an interval shorter than `log q`,
`W(g(· − k log q), g(· − l log q)) = log q · ‖g‖² · Σ_i β_i^{|k−l|}`. -/
theorem W_curveConfig_translate_narrow {g : ℝ → ℂ} {A : ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Set.Icc (-(A / 2)) (A / 2)) (hAL : A < Real.log D.q) (k l : ℕ) :
    (D.curveConfig hD).W (translate (k * Real.log D.q) g) (translate (l * Real.log D.q) g) =
      ((Real.log D.q * ∫ u, ‖g u‖ ^ 2 : ℝ) : ℂ) * (D.trace (Nat.dist k l) : ℂ) := by
  have hL := D.log_q_pos
  have hgc : HasCompactSupport g := RHTower.hasCompactSupport_of_tsupport_subset_Icc hgs
  rw [D.W_curveConfig hD (translate_contDiff hg _) (translate_hasCompactSupport hgc _)
    (translate_contDiff hg _).continuous (translate_hasCompactSupport hgc _)]
  have hKs := EF.tsupport_weilTest_subset hgs hgs
  -- only the lag `k − l` survives
  have hsingle : ∀ i, ∑' m : ℤ, EF.weilTest (translate (k * Real.log D.q) g)
      (translate (l * Real.log D.q) g) (m * Real.log D.q) * D.β i ^ m =
        EF.weilTest g g 0 * D.β i ^ ((k : ℤ) - l) := by
    intro i
    rw [tsum_eq_single ((k : ℤ) - l)]
    · rw [weilTest_translate]; push_cast; ring_nf
    · intro m hm
      rw [weilTest_translate]
      have hz : EF.weilTest g g ((m : ℝ) * Real.log D.q -
          ((k : ℝ) * Real.log D.q - (l : ℝ) * Real.log D.q)) = 0 := by
        by_contra hne
        have hmem := hKs (subset_tsupport _ hne)
        have hj : ((m - ((k : ℤ) - l) : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hm
        have h1 : (1 : ℝ) ≤ |((m - ((k : ℤ) - l) : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hm)
        have heq : (m : ℝ) * Real.log D.q - ((k : ℝ) * Real.log D.q - (l : ℝ) * Real.log D.q) =
            ((m - ((k : ℤ) - l) : ℤ) : ℝ) * Real.log D.q := by
          push_cast; ring
        rw [heq] at hmem
        have h2 : |((m - ((k : ℤ) - l) : ℤ) : ℝ) * Real.log D.q| ≤ A := abs_le.mpr hmem
        rw [abs_mul, abs_of_pos hL] at h2
        nlinarith
      rw [hz, zero_mul]
  simp only [hsingle]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_zpow_eq_trace, natAbs_sub_eq_dist]
  have h0 : EF.weilTest g g 0 = ((∫ u, ‖g u‖ ^ 2 : ℝ) : ℂ) := by
    rw [RHTower.weilTest_apply, ← integral_complex_ofReal]
    congr 1
    funext t
    rw [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h0]
  push_cast
  ring

/-- **The `q`-tower is the Frobenius span.** For a test supported in an interval shorter than
`log q`, the Gram matrix of the translates `g(· − k log q)`, `k < n`, on the scaling surface of the
curve is `log q · ‖g‖²` times the Frobenius span Gram matrix. -/
theorem curve_towerGram_eq_smul_spanGram {g : ℝ → ℂ} {A : ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Set.Icc (-(A / 2)) (A / 2)) (hAL : A < Real.log D.q) (n : ℕ) :
    zeroGram (D.curveConfig hD) (fun k : Fin n => translate (((k : ℕ) : ℝ) * Real.log D.q) g) =
      ((Real.log D.q * ∫ u, ‖g u‖ ^ 2 : ℝ) : ℂ) • D.spanGram n := by
  ext k l
  simp only [zeroGram, Matrix.smul_apply, spanGram, smul_eq_mul]
  exact D.W_curveConfig_translate_narrow hD hg hgs hAL k l

/-- **The tower Pontryagin law of a curve.** On the scaling surface of a curve datum in the strip,
the `q`-tower of a nonzero narrow test has at most as many negative squares as there are distinct
eigenvalues outside the unit circle, with equality from window `2g` on: the tower defect is the
Frobenius span defect. -/
theorem curve_tower_pontryagin_law {g : ℝ → ℂ} {A : ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Set.Icc (-(A / 2)) (A / 2)) (hAL : A < Real.log D.q)
    (hg0 : 0 < ∫ u, ‖g u‖ ^ 2) :
    (∀ n, hermNegIndex (zeroGram (D.curveConfig hD)
        (fun k : Fin n => translate (((k : ℕ) : ℝ) * Real.log D.q) g)) ≤ D.outerSpectrum.card) ∧
      ∀ n, Fintype.card ι ≤ n → hermNegIndex (zeroGram (D.curveConfig hD)
        (fun k : Fin n => translate (((k : ℕ) : ℝ) * Real.log D.q) g)) =
          D.outerSpectrum.card := by
  have hc : 0 < Real.log D.q * ∫ u, ‖g u‖ ^ 2 := mul_pos D.log_q_pos hg0
  have heq : ∀ n, hermNegIndex (zeroGram (D.curveConfig hD)
      (fun k : Fin n => translate (((k : ℕ) : ℝ) * Real.log D.q) g)) =
        hermNegIndex (D.spanGram n) := fun n => by
    rw [D.curve_towerGram_eq_smul_spanGram hD hg hgs hAL n, hermNegIndex_ofReal_smul hc]
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · rw [heq]; exact D.pontryagin_law_curve.1 n
  · rw [heq]; exact D.pontryagin_law_curve.2 n hn

end CurveDatum

/-- **The golden fake curve on the scaling surface.** The `5`-tower of a nonzero narrow test has
exactly one negative square from window `2` on: the one outer eigenvalue `φ`. -/
theorem goldenDatum_tower_negIndex {g : ℝ → ℂ} {A : ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Set.Icc (-(A / 2)) (A / 2)) (hAL : A < Real.log goldenDatum.q)
    (hg0 : 0 < ∫ u, ‖g u‖ ^ 2) {n : ℕ} (hn : 2 ≤ n) :
    hermNegIndex (zeroGram (goldenDatum.curveConfig goldenDatum_strip)
      (fun k : Fin n => translate (((k : ℕ) : ℝ) * Real.log goldenDatum.q) g)) = 1 := by
  rw [goldenDatum.curve_towerGram_eq_smul_spanGram goldenDatum_strip hg hgs hAL n,
    hermNegIndex_ofReal_smul (mul_pos goldenDatum.log_q_pos hg0)]
  exact goldenDatum_negIndex_spanGram hn

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
