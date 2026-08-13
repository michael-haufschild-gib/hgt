import GaloisForLFunctions.RHTower.FieldOneFiniteStageBruhatRapidDecay
import GaloisForLFunctions.RHTower.FieldOneFiniteStageBruhatOrbitCounting

/-!
# Sharp small-module growth of finite-stage Bruhat periodization

This file proves the small-module half of Connes--Marcolli Lemma 2.29 on the
literal semilocal carrier.  Compact nonarchimedean support supplies one
denominator uniformly over the norm-one torus.  Contributing rational
`S`-units in a logarithmic prefix have cardinality `O(B ^ |S|)`.  The
remaining tail is injected into successive prefix boxes and summed against
the order-one archimedean Schwartz decay.

The resulting exponent is exactly `|S|`, i.e. `m - 1` when the real place is
included in Connes--Marcolli's `m = Card S` convention.  No counting premise,
asymptotic hypothesis, spectral premise, or numerical computation occurs.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

private theorem summable_succ_pow_mul_exp_neg
    (s : ℕ) :
    Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ s) * Real.exp (-(n : ℝ))) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul s
    (by norm_num : (0 : ℝ) < 1)
  have hinj : Function.Injective (fun n : ℕ => n + 1) := by
    intro m n hmn
    exact Nat.add_right_cancel hmn
  have hs := h.comp_injective hinj
  have he := hs.mul_left (Real.exp 1)
  have he' : Summable
      (fun n : ℕ => ((n : ℝ) + 1) ^ s * Real.exp (-(n : ℝ))) :=
    he.congr fun n => by
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      calc
        Real.exp 1 * ((↑n + 1) ^ s * Real.exp (-1 * (↑n + 1))) =
            (↑n + 1) ^ s *
              (Real.exp 1 * Real.exp (-1 * (↑n + 1))) := by ring
        _ = (↑n + 1) ^ s * Real.exp (1 + (-1 * (↑n + 1))) := by
          rw [Real.exp_add]
        _ = (↑n + 1) ^ s * Real.exp (-(n : ℝ)) := by
          congr 2
          ring
  simpa only [Nat.cast_add, Nat.cast_one] using he'

private theorem tsum_finset_subtype_const
    {α : Type*} (A : Finset α) (c : ℝ) :
    (∑' _ : ↥A, c) = (A.card : ℝ) * c := by
  rw [tsum_fintype]
  simp [nsmul_eq_mul]

/-- Uniform sharp logarithmic growth for the absolute orbit sum of a pure
Bruhat--Schwartz tensor. -/
theorem fieldOneFiniteStageBruhatPureTensor_norm_tsum_uniform_logGrowth
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : FieldOneFiniteStageNormOneTorus S) (t : ℝ), t ≤ 0 →
      (∑' q : fieldOneSUnitSubgroup S,
        ‖fieldOneFiniteStageBruhatPureTensorOrbit S f phi
          (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t) q‖) ≤
        C * (-t + 2) ^ Fintype.card ↥S := by
  classical
  obtain ⟨Bphi, hBphi⟩ :=
    fieldOneFiniteStageFiniteBruhat_exists_norm_bound S phi
  obtain ⟨d, hd, hden⟩ :=
    fieldOneFiniteStageFiniteBruhat_exists_uniformNormOneIntegerDenominator S phi
  let L := fieldOneFiniteStageDenominatorExponentLower S d
  let K := fieldOneSUnitLogBoxPolynomialConstant S L
  let s := Fintype.card ↥S
  let M0 := Bphi * (SchwartzMap.seminorm ℂ 0 0) f
  let M1 := Bphi * (SchwartzMap.seminorm ℂ 1 0) f
  let a : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ) ^ s) * Real.exp (-(n : ℝ))
  let Z := ∑' n : ℕ, a n
  let C := M0 * K + M1 * K * Z
  have hBphi0 : 0 ≤ Bphi :=
    (norm_nonneg (phi.1 0)).trans (hBphi 0)
  have hK : 0 ≤ K :=
    (fieldOneSUnitLogBoxPolynomialConstant_pos S L).le
  have hM0 : 0 ≤ M0 := mul_nonneg hBphi0
    (apply_nonneg (SchwartzMap.seminorm ℂ 0 0) f)
  have hM1 : 0 ≤ M1 := mul_nonneg hBphi0
    (apply_nonneg (SchwartzMap.seminorm ℂ 1 0) f)
  have ha_nonneg : ∀ n, 0 ≤ a n := fun n => mul_nonneg
    (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le
  have ha_sum : Summable a := by
    simpa [a, s] using summable_succ_pow_mul_exp_neg s
  have hZ : 0 ≤ Z := tsum_nonneg ha_nonneg
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hM0 hK)
    (mul_nonneg (mul_nonneg hM1 hK) hZ)
  refine ⟨C, hC, fun k t ht => ?_⟩
  let B : ℝ := -t
  have hB : 0 ≤ B := by dsimp [B]; linarith
  let b : (v : ↥S) → (v.1.adicCompletion ℚ)ˣ := fun v => (k v).1
  let u0 : FieldOneFiniteStageIdele S :=
    fieldOneFiniteStageBruhatLogRayIdele S b 0
  let u : FieldOneFiniteStageIdele S :=
    fieldOneFiniteStageBruhatLogRayIdele S b t
  let P : Set (fieldOneSUnitSubgroup S) :=
    {q | phi.1 (fun v =>
      algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
        (b v : v.1.adicCompletion ℚ)) ≠ 0}
  let H : Set (fieldOneSUnitSubgroup S) :=
    fieldOneFiniteStageFiniteBruhatLogOrbit S phi u0 B
  have hHfinite : H.Finite :=
    fieldOneFiniteStageFiniteBruhatLogOrbit_finite S phi u0 B
  let HF : Finset (fieldOneSUnitSubgroup S) := hHfinite.toFinset
  let F : fieldOneSUnitSubgroup S → ℂ := fun q =>
    fieldOneFiniteStageBruhatPureTensorOrbit S f phi u q
  have hFsummable : Summable (fun q => ‖F q‖) := by
    simpa [F, u] using
      fieldOneFiniteStageBruhatPureTensorOrbit_summable S f phi u
  have hsupportF : Function.support F ⊆ P := by
    intro q hq
    by_contra hnot
    have hphi : phi.1 (fun v =>
        algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
          (b v : v.1.adicCompletion ℚ)) = 0 := by
      simpa [P] using hnot
    apply hq
    change f (Real.exp t * (((q.1 : ℚ) : ℝ))) *
      phi.1 (fun v =>
        algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
          (b v : v.1.adicCompletion ℚ)) = 0
    rw [hphi, mul_zero]
  have hcard (R : ℝ) (hR : 0 ≤ R) :
      ((fieldOneFiniteStageFiniteBruhatLogOrbit S phi u0 R).ncard : ℝ) ≤
        K * (R + 1) ^ s := by
    have hsubset :
        fieldOneFiniteStageFiniteBruhatLogOrbit S phi u0 R ⊆
          fieldOneSUnitLogBox S L R := by
      apply fieldOneFiniteStageFiniteBruhatLogOrbit_subset_logBox
        S phi u0 R d hd
      intro q hq
      exact hden k q (by simpa [u0, b,
        fieldOneFiniteStageBruhatLogRayIdele] using hq)
    have hncard :
        (fieldOneFiniteStageFiniteBruhatLogOrbit S phi u0 R).ncard ≤
          (fieldOneSUnitLogBox S L R).ncard :=
      Set.ncard_le_ncard hsubset (fieldOneSUnitLogBox_finite S L R)
    exact (by exact_mod_cast hncard :
        ((fieldOneFiniteStageFiniteBruhatLogOrbit S phi u0 R).ncard : ℝ) ≤
          ((fieldOneSUnitLogBox S L R).ncard : ℝ)).trans
      (fieldOneSUnitLogBox_ncard_cast_le_polynomial S L R hR)
  have hpoint0 (q : fieldOneSUnitSubgroup S) : ‖F q‖ ≤ M0 := by
    change ‖f ((u.1 : ℝ) * ((q.1 : ℚ) : ℝ)) *
      phi.1 (fun v =>
        algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
          (u.2 v : v.1.adicCompletion ℚ))‖ ≤ M0
    rw [norm_mul]
    exact (mul_le_mul
      (SchwartzMap.norm_le_seminorm ℂ f _)
      (hBphi _) (norm_nonneg _)
      (apply_nonneg (SchwartzMap.seminorm ℂ 0 0) f)).trans_eq (by
        dsimp [M0]
        ring)
  have hhead :
      (∑ q ∈ HF, ‖F q‖) ≤ M0 * K * (B + 2) ^ s := by
    calc
      (∑ q ∈ HF, ‖F q‖) ≤ ∑ _q ∈ HF, M0 :=
        Finset.sum_le_sum fun q _ => hpoint0 q
      _ = (HF.card : ℝ) * M0 := by simp [nsmul_eq_mul]
      _ = (H.ncard : ℝ) * M0 := by
        rw [Set.ncard_eq_toFinset_card H hHfinite]
      _ ≤ (K * (B + 1) ^ s) * M0 :=
        mul_le_mul_of_nonneg_right (hcard B hB) hM0
      _ ≤ M0 * K * (B + 2) ^ s := by
        have hp : (B + 1) ^ s ≤ (B + 2) ^ s :=
          pow_le_pow_left₀ (by linarith) (by linarith) s
        calc
          (K * (B + 1) ^ s) * M0 = (M0 * K) * (B + 1) ^ s := by ring
          _ ≤ (M0 * K) * (B + 2) ^ s :=
            mul_le_mul_of_nonneg_left hp (mul_nonneg hM0 hK)
  let HC : Set {q // q ∉ HF} := {q | q.1 ∈ P}
  have hsupport_compl :
      Function.support (fun q : {q // q ∉ HF} => ‖F q.1‖) ⊆ HC := by
    intro q hq
    have hFq : F q.1 ≠ 0 := by
      intro hz
      apply hq
      simp [hz]
    exact hsupportF hFq
  let prefixSet : ℕ → Set (fieldOneSUnitSubgroup S) := fun n =>
    fieldOneFiniteStageFiniteBruhatLogOrbit S phi u0
      (B + (n : ℝ) + 1)
  have hprefixFinite : ∀ n, (prefixSet n).Finite := fun n =>
    fieldOneFiniteStageFiniteBruhatLogOrbit_finite S phi u0
      (B + (n : ℝ) + 1)
  let prefixFinset : ℕ → Finset (fieldOneSUnitSubgroup S) := fun n =>
    (hprefixFinite n).toFinset
  let shellIndex : HC → ℕ := fun q =>
    ⌊Real.log |(((q.1.1.1 : ℚˣ) : ℚ) : ℝ)| - B⌋₊
  have htailLog (q : HC) :
      B < Real.log |(((q.1.1.1 : ℚˣ) : ℚ) : ℝ)| := by
    have hnotH : q.1.1 ∉ H := by
      intro hmem
      exact q.1.2 ((hHfinite.mem_toFinset).2 hmem)
    exact lt_of_not_ge fun hle => hnotH ⟨q.2, hle⟩
  have hprefixMem (q : HC) : q.1.1 ∈ prefixFinset (shellIndex q) := by
    apply (hprefixFinite (shellIndex q)).mem_toFinset.mpr
    refine ⟨q.2, ?_⟩
    have hdiff0 : 0 ≤
        Real.log |(((q.1.1.1 : ℚˣ) : ℚ) : ℝ)| - B := by
      linarith [htailLog q]
    have hupp := Nat.lt_floor_add_one
      (Real.log |(((q.1.1.1 : ℚˣ) : ℚ) : ℝ)| - B)
    change Real.log |(((q.1.1.1 : ℚˣ) : ℚ) : ℝ)| ≤
      B + (shellIndex q : ℝ) + 1
    dsimp [shellIndex]
    linarith
  let e : HC → (Σ n : ℕ, ↥(prefixFinset n)) := fun q =>
    ⟨shellIndex q, ⟨q.1.1, hprefixMem q⟩⟩
  have he : Function.Injective e := by
    intro q r hqr
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.2.1) hqr
  have htailPoint (q : HC) :
      ‖F q.1.1‖ ≤ M1 * Real.exp (-(shellIndex q : ℝ)) := by
    let x : ℝ := Real.exp t * (((q.1.1.1 : ℚˣ) : ℚ) : ℝ)
    have hdiff0 : 0 ≤
        Real.log |(((q.1.1.1 : ℚˣ) : ℚ) : ℝ)| - B := by
      linarith [htailLog q]
    have hfloor := Nat.floor_le hdiff0
    have hqabs : 0 < |(((q.1.1.1 : ℚˣ) : ℚ) : ℝ)| := by
      rw [abs_pos]
      exact_mod_cast Units.ne_zero q.1.1.1
    have hnx : Real.exp (shellIndex q : ℝ) ≤ ‖x‖ := by
      have hexp := Real.exp_le_exp.mpr hfloor
      calc
        Real.exp (shellIndex q : ℝ) ≤
            Real.exp
              (Real.log |(((q.1.1.1 : ℚˣ) : ℚ) : ℝ)| - B) := by
          simpa [shellIndex] using hexp
        _ = Real.exp t * |(((q.1.1.1 : ℚˣ) : ℚ) : ℝ)| := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hqabs]
          rw [show -B = t by dsimp [B]; ring]
          ring
        _ = ‖x‖ := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos t)]
    have hxpos : 0 < ‖x‖ := (Real.exp_pos _).trans_le hnx
    have hsem := SchwartzMap.norm_pow_mul_le_seminorm ℂ f 1 x
    have hfdecay :
        ‖f x‖ ≤ (SchwartzMap.seminorm ℂ 1 0) f *
          Real.exp (-(shellIndex q : ℝ)) := by
      calc
        ‖f x‖ ≤ (SchwartzMap.seminorm ℂ 1 0) f / ‖x‖ := by
          apply (le_div_iff₀ hxpos).2
          simpa [mul_comm] using hsem
        _ ≤ (SchwartzMap.seminorm ℂ 1 0) f /
            Real.exp (shellIndex q : ℝ) :=
          div_le_div_of_nonneg_left
            (apply_nonneg (SchwartzMap.seminorm ℂ 1 0) f)
            (Real.exp_pos _) hnx
        _ = (SchwartzMap.seminorm ℂ 1 0) f *
            Real.exp (-(shellIndex q : ℝ)) := by
          rw [div_eq_mul_inv, Real.exp_neg]
    change ‖f ((u.1 : ℝ) * (((q.1.1.1 : ℚˣ) : ℚ) : ℝ)) *
      phi.1 (fun v =>
        algebraMap ℚ (v.1.adicCompletion ℚ) (q.1.1.1 : ℚ) *
          (u.2 v : v.1.adicCompletion ℚ))‖ ≤ _
    rw [norm_mul]
    calc
      ‖f ((u.1 : ℝ) * (((q.1.1.1 : ℚˣ) : ℚ) : ℝ))‖ *
          ‖phi.1 (fun v =>
            algebraMap ℚ (v.1.adicCompletion ℚ) (q.1.1.1 : ℚ) *
              (u.2 v : v.1.adicCompletion ℚ))‖ ≤
          ((SchwartzMap.seminorm ℂ 1 0) f *
            Real.exp (-(shellIndex q : ℝ))) * Bphi := by
        apply mul_le_mul
        · simpa [x, u, b, fieldOneFiniteStageBruhatLogRayIdele] using hfdecay
        · exact hBphi _
        · exact norm_nonneg _
        · exact mul_nonneg
            (apply_nonneg (SchwartzMap.seminorm ℂ 1 0) f)
            (Real.exp_pos _).le
      _ = M1 * Real.exp (-(shellIndex q : ℝ)) := by
        dsimp [M1]
        ring
  let G : (Σ n : ℕ, ↥(prefixFinset n)) → ℝ := fun z =>
    M1 * Real.exp (-(z.1 : ℝ))
  have hGnonneg : ∀ z, 0 ≤ G z := fun z =>
    mul_nonneg hM1 (Real.exp_pos _).le
  have hGinner : ∀ n, Summable (fun q : ↥(prefixFinset n) => G ⟨n, q⟩) := by
    intro n
    exact Summable.of_finite
  have hGinnerEq (n : ℕ) :
      (∑' q : ↥(prefixFinset n), G ⟨n, q⟩) =
        ((prefixFinset n).card : ℝ) *
          (M1 * Real.exp (-(n : ℝ))) := by
    simpa [G] using
      tsum_finset_subtype_const (prefixFinset n)
        (M1 * Real.exp (-(n : ℝ)))
  have hprefixCard (n : ℕ) :
      ((prefixFinset n).card : ℝ) ≤
        K * (B + (n : ℝ) + 2) ^ s := by
    rw [show (prefixFinset n).card = (prefixSet n).ncard by
      dsimp [prefixFinset]
      exact (Set.ncard_eq_toFinset_card (prefixSet n) (hprefixFinite n)).symm]
    have hR : 0 ≤ B + (n : ℝ) + 1 := by positivity
    calc
      ((prefixSet n).ncard : ℝ) ≤
          K * ((B + (n : ℝ) + 1) + 1) ^ s := by
        simpa only [prefixSet] using hcard (B + (n : ℝ) + 1) hR
      _ = K * (B + (n : ℝ) + 2) ^ s := by
        congr 2
        ring
  have hpolyFactor (n : ℕ) :
      (B + (n : ℝ) + 2) ^ s ≤
        (B + 2) ^ s * (((n + 1 : ℕ) : ℝ) ^ s) := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    nlinarith [mul_nonneg hB (Nat.cast_nonneg n)]
  have houterBound (n : ℕ) :
      (∑' q : ↥(prefixFinset n), G ⟨n, q⟩) ≤
        (M1 * K * (B + 2) ^ s) * a n := by
    rw [hGinnerEq]
    calc
      ((prefixFinset n).card : ℝ) *
          (M1 * Real.exp (-(n : ℝ))) ≤
          (K * (B + (n : ℝ) + 2) ^ s) *
            (M1 * Real.exp (-(n : ℝ))) :=
        mul_le_mul_of_nonneg_right (hprefixCard n)
          (mul_nonneg hM1 (Real.exp_pos _).le)
      _ ≤ (M1 * K * (B + 2) ^ s) * a n := by
        dsimp [a]
        calc
          (K * (B + (n : ℝ) + 2) ^ s) *
              (M1 * Real.exp (-(n : ℝ))) =
              (M1 * K * Real.exp (-(n : ℝ))) *
                (B + (n : ℝ) + 2) ^ s := by ring
          _ ≤ (M1 * K * Real.exp (-(n : ℝ))) *
              ((B + 2) ^ s * (((n + 1 : ℕ) : ℝ) ^ s)) :=
            mul_le_mul_of_nonneg_left (hpolyFactor n)
              (mul_nonneg (mul_nonneg hM1 hK) (Real.exp_pos _).le)
          _ = (M1 * K * (B + 2) ^ s) *
              (((n + 1 : ℕ) : ℝ) ^ s * Real.exp (-(n : ℝ))) := by ring
  have houterNonneg (n : ℕ) :
      0 ≤ ∑' q : ↥(prefixFinset n), G ⟨n, q⟩ :=
    tsum_nonneg fun _ => hGnonneg _
  have hmajorant : Summable
      (fun n : ℕ => (M1 * K * (B + 2) ^ s) * a n) :=
    ha_sum.mul_left _
  have houter : Summable
      (fun n => ∑' q : ↥(prefixFinset n), G ⟨n, q⟩) :=
    Summable.of_nonneg_of_le houterNonneg houterBound hmajorant
  have hGsum : Summable G :=
    (summable_sigma_of_nonneg hGnonneg).2 ⟨hGinner, houter⟩
  have hGtsum :
      (∑' z, G z) ≤ M1 * K * (B + 2) ^ s * Z := by
    rw [hGsum.tsum_sigma' hGinner]
    calc
      (∑' n, ∑' q : ↥(prefixFinset n), G ⟨n, q⟩) ≤
          ∑' n, (M1 * K * (B + 2) ^ s) * a n :=
        houter.tsum_le_tsum houterBound hmajorant
      _ = M1 * K * (B + 2) ^ s * Z := by
        rw [tsum_mul_left]
  have htailSummable : Summable (fun q : HC => ‖F q.1.1‖) := by
    exact hFsummable.comp_injective fun q r hqr => by
      apply Subtype.ext
      apply Subtype.ext
      exact hqr
  have htail :
      (∑' q : HC, ‖F q.1.1‖) ≤ M1 * K * (B + 2) ^ s * Z := by
    apply (htailSummable.tsum_le_tsum_of_inj e he
      (fun z _ => hGnonneg z)
      (fun q => by simpa [G, e] using htailPoint q)
      hGsum).trans
    exact hGtsum
  have hsplit := hFsummable.sum_add_tsum_subtype_compl HF
  change (∑' q, ‖F q‖) ≤ _
  rw [← hsplit]
  calc
    (∑ q ∈ HF, ‖F q‖) + ∑' q : {q // q ∉ HF}, ‖F q.1‖ =
        (∑ q ∈ HF, ‖F q‖) + ∑' q : HC, ‖F q.1.1‖ := by
      congr 1
      exact (tsum_subtype_eq_of_support_subset hsupport_compl).symm
    _ ≤ M0 * K * (B + 2) ^ s +
          M1 * K * (B + 2) ^ s * Z := add_le_add hhead htail
    _ = C * (-t + 2) ^ Fintype.card ↥S := by
      dsimp [C, B, s]
      ring

/-- Uniform sharp logarithmic growth for a pure Bruhat--Schwartz tensor. -/
theorem fieldOneFiniteStageBruhatPureTensor_uniform_logGrowth
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : FieldOneFiniteStageNormOneTorus S) (t : ℝ), t ≤ 0 →
      ‖fieldOneFiniteStageBruhatPeriodization S (f ⊗ₜ[ℂ] phi)
          (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ ≤
        C * (-t + 2) ^ Fintype.card ↥S := by
  obtain ⟨C, hC, hbound⟩ :=
    fieldOneFiniteStageBruhatPureTensor_norm_tsum_uniform_logGrowth S f phi
  refine ⟨C, hC, fun k t ht => ?_⟩
  rw [fieldOneFiniteStageBruhatPeriodization]
  exact (norm_tsum_le_tsum_norm
    (fieldOneFiniteStageBruhatPureTensorOrbit_summable S f phi
      (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t))).trans
    (hbound k t ht)

/-- Uniform sharp logarithmic growth for the absolute orbit sum of every
finite-stage Bruhat--Schwartz tensor. -/
theorem fieldOneFiniteStageBruhatTensor_norm_tsum_uniform_logGrowth
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : FieldOneFiniteStageNormOneTorus S) (t : ℝ), t ≤ 0 →
      (∑' q : fieldOneSUnitSubgroup S,
        ‖fieldOneFiniteStageBruhatOrbit S x
          (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t) q‖) ≤
        C * (-t + 2) ^ Fintype.card ↥S := by
  induction x using TensorProduct.induction_on with
  | zero =>
      refine ⟨0, le_rfl, fun k t ht => ?_⟩
      simp [fieldOneFiniteStageBruhatOrbit]
  | tmul f phi =>
      simpa only [fieldOneFiniteStageBruhatOrbit_tmul] using
        fieldOneFiniteStageBruhatPureTensor_norm_tsum_uniform_logGrowth S f phi
  | add x y hx hy =>
      obtain ⟨Cx, hCx, hxbound⟩ := hx
      obtain ⟨Cy, hCy, hybound⟩ := hy
      refine ⟨Cx + Cy, add_nonneg hCx hCy, fun k t ht => ?_⟩
      let u := fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t
      have hsx := fieldOneFiniteStageBruhatOrbit_summable S x u
      have hsy := fieldOneFiniteStageBruhatOrbit_summable S y u
      have hsxy := fieldOneFiniteStageBruhatOrbit_summable S (x + y) u
      calc
        (∑' q, ‖fieldOneFiniteStageBruhatOrbit S (x + y) u q‖) ≤
            ∑' q, (‖fieldOneFiniteStageBruhatOrbit S x u q‖ +
              ‖fieldOneFiniteStageBruhatOrbit S y u q‖) := by
          apply hsxy.tsum_le_tsum
          · intro q
            simpa [fieldOneFiniteStageBruhatOrbit] using
              norm_add_le (fieldOneFiniteStageBruhatOrbit S x u q)
                (fieldOneFiniteStageBruhatOrbit S y u q)
          · exact hsx.add hsy
        _ = (∑' q, ‖fieldOneFiniteStageBruhatOrbit S x u q‖) +
              ∑' q, ‖fieldOneFiniteStageBruhatOrbit S y u q‖ :=
          hsx.tsum_add hsy
        _ ≤ Cx * (-t + 2) ^ Fintype.card ↥S +
              Cy * (-t + 2) ^ Fintype.card ↥S :=
          add_le_add (hxbound k t ht) (hybound k t ht)
        _ = (Cx + Cy) * (-t + 2) ^ Fintype.card ↥S := by ring

/-- Uniform sharp logarithmic growth for every finite-stage Bruhat--Schwartz
tensor.  This is the full small-module assertion of Connes--Marcolli
Lemma 2.29. -/
theorem fieldOneFiniteStageBruhatTensor_uniform_logGrowth
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : FieldOneFiniteStageNormOneTorus S) (t : ℝ), t ≤ 0 →
      ‖fieldOneFiniteStageBruhatPeriodization S x
          (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ ≤
        C * (-t + 2) ^ Fintype.card ↥S := by
  induction x using TensorProduct.induction_on with
  | zero =>
      refine ⟨0, le_rfl, fun k t ht => ?_⟩
      simp
  | tmul f phi =>
      exact fieldOneFiniteStageBruhatPureTensor_uniform_logGrowth S f phi
  | add x y hx hy =>
      obtain ⟨Cx, hCx, hxbound⟩ := hx
      obtain ⟨Cy, hCy, hybound⟩ := hy
      refine ⟨Cx + Cy, add_nonneg hCx hCy, fun k t ht => ?_⟩
      rw [fieldOneFiniteStageBruhatPeriodization_add]
      calc
        ‖fieldOneFiniteStageBruhatPeriodization S x
              (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t) +
            fieldOneFiniteStageBruhatPeriodization S y
              (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ ≤
            ‖fieldOneFiniteStageBruhatPeriodization S x
              (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ +
            ‖fieldOneFiniteStageBruhatPeriodization S y
              (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ :=
          norm_add_le _ _
        _ ≤ Cx * (-t + 2) ^ Fintype.card ↥S +
            Cy * (-t + 2) ^ Fintype.card ↥S :=
          add_le_add (hxbound k t ht) (hybound k t ht)
        _ = (Cx + Cy) * (-t + 2) ^ Fintype.card ↥S := by ring

/-- Source-normalized form of the small-module estimate: on the logarithmic
ray, periodization is uniformly `O(|t| ^ |S|)` as `t → -∞`. -/
theorem fieldOneFiniteStageBruhatTensor_uniform_logGrowth_sourceForm
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : FieldOneFiniteStageNormOneTorus S) (t : ℝ), t ≤ -1 →
      ‖fieldOneFiniteStageBruhatPeriodization S x
          (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ ≤
        C * |t| ^ Fintype.card ↥S := by
  obtain ⟨C, hC, hbound⟩ :=
    fieldOneFiniteStageBruhatTensor_uniform_logGrowth S x
  let s := Fintype.card ↥S
  refine ⟨C * 3 ^ s, mul_nonneg hC (pow_nonneg (by norm_num) _),
    fun k t ht => ?_⟩
  have ht0 : t ≤ 0 := ht.trans (by norm_num)
  have hbase : -t + 2 ≤ 3 * |t| := by
    rw [abs_of_nonpos ht0]
    linarith
  have habs : 0 ≤ |t| := abs_nonneg _
  calc
    ‖fieldOneFiniteStageBruhatPeriodization S x
        (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ ≤
        C * (-t + 2) ^ s := hbound k t ht0
    _ ≤ C * (3 * |t|) ^ s :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) hbase s) hC
    _ = (C * 3 ^ s) * |t| ^ s := by rw [mul_pow]; ring

/-- Exact finite-stage Connes--Marcolli Lemma 2.29: absolute convergence,
sharp small-module logarithmic growth, and arbitrary-order large-module
decay, bundled on the literal semilocal carrier. -/
theorem fieldOneFiniteStage_connesMarcolli_lemma_2_29
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    (∀ u : FieldOneFiniteStageIdele S,
      Summable (fun q : fieldOneSUnitSubgroup S =>
        ‖fieldOneFiniteStageBruhatOrbit S x u q‖)) ∧
    (∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : FieldOneFiniteStageNormOneTorus S) (t : ℝ), t ≤ -1 →
      ‖fieldOneFiniteStageBruhatPeriodization S x
          (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ ≤
        C * |t| ^ Fintype.card ↥S) ∧
    (∀ a : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : FieldOneFiniteStageNormOneTorus S) (t : ℝ), 0 ≤ t →
      ‖fieldOneFiniteStageBruhatPeriodization S x
          (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ ≤
        C * Real.exp t ^ (-a)) := by
  refine ⟨fieldOneFiniteStageBruhatOrbit_summable S x,
    fieldOneFiniteStageBruhatTensor_uniform_logGrowth_sourceForm S x, ?_⟩
  exact fieldOneFiniteStageBruhatTensor_uniform_rapidDecay S x

end

end GaloisForLFunctions.RHTower
