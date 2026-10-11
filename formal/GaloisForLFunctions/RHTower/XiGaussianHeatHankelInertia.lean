import GaloisForLFunctions.RHTower.XiGaussianHeatHankelWindowCeiling
import GaloisForLFunctions.HTGeometry.SymmetricPolynomialJets

/-!
# Complete inertia of the heat Hankel form

The heat Hankel form `H_a(P, R) = Σ_q e^{-a w_q} P(w_q) \overline{R(\overline{w_q})}` on `ℂ[X]` has
negative index equal to the number `#U ∈ ℕ ∪ {∞}` of off-line zero quadruples
(`heatHankel_negativeIndex_eq_card`, `heatHankel_negative_subspace_of_infinite`).  This file
supplies the other two parts of its inertia, unconditionally:

* **Nondegeneracy** (`eq_zero_of_forall_heatHankel_eq_zero`): if `H_a(P, R) = 0` for every `R`, then
  `P = 0`.
* **Infinite positive index** (`exists_heatHankel_pos_subspace`): for every `n` there is an
  `n`-dimensional subspace on which `Re H_a` is positive definite.

So `(ℂ[X], H_a)` is a nondegenerate Hermitian space with infinite positive index and negative index
`#U`, a Pontryagin space `Π_{#U}` when `#U < ∞`, and RH holds iff it is positive definite.

Both proofs isolate real heat frequencies `v = γ²` of real zeros (Hardy's theorem supplies
infinitely many) with root polynomials killing every other frequency of real part `≤ Λ`.  They control
the frequencies above `Λ` by the admissible levels of `exists_heatLevel`.
-/

open Complex Polynomial
open GaloisForLFunctions.HTGeometry (conjPoly eval_conjPoly)

namespace RHTower

noncomputable section

/-! ## Admissible levels at every heat time -/

/-- For every `a > 0` there are admissible levels above any prescribed height. -/
theorem exists_heatLevel_at {a C : ℝ} (ha : 0 < a) (hC : 0 < C) (η U : ℝ) :
    ∃ Λ : ℝ, U ≤ Λ ∧ 0 ≤ Λ ∧ ∃ k : ℕ, (heatFrequenciesBelow Λ).card ≤ k ∧
      ((2 * k + 3 : ℕ) : ℝ) ≤ a * (1 + Λ) ∧
      ((2 * k + 3 : ℕ) : ℝ) * Real.log (C * (1 + Λ)) + Real.log (1 / η) ≤ a * Λ := by
  obtain ⟨_, a₀, ha₀, hlev⟩ := exists_heatLevel hC η U
  obtain ⟨Λ, hU, hΛ, k, hk, h1, h2, _⟩ := hlev (min a a₀) (lt_min ha ha₀) (min_le_right _ _)
  have hmin : min a a₀ ≤ a := min_le_left _ _
  refine ⟨Λ, hU, hΛ, k, hk, h1.trans (mul_le_mul_of_nonneg_right hmin (by linarith)),
    h2.trans (mul_le_mul_of_nonneg_right hmin hΛ)⟩

/-- Above the level, `e^{-aW} (C₀(1 + |w|))^j (1 + |w|)^e ≤ η / (1 + |w|)` when
`j + e + 1 ≤ 2k + 3`. -/
theorem exp_mul_level_weight_le_of_exponent {a Λ C₀ η : ℝ} {j e k : ℕ} (hC₀ : 1 ≤ C₀)
    (hη : 0 < η) (hΛ : 0 ≤ Λ) (hjk : j + e + 1 ≤ 2 * k + 3)
    (h1 : ((2 * k + 3 : ℕ) : ℝ) ≤ a * (1 + Λ))
    (h2 : ((2 * k + 3 : ℕ) : ℝ) * Real.log (2 * C₀ * (1 + Λ)) + Real.log (1 / η) ≤ a * Λ)
    {q : XiZeroCopy} (hq : Λ < (xiHeatFrequency q).re) :
    Real.exp (-(a * (xiHeatFrequency q).re)) *
        ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ j * (1 + ‖xiHeatFrequency q‖) ^ e) ≤
      η * (1 / (1 + ‖xiHeatFrequency q‖)) := by
  set w := xiHeatFrequency q
  set W := w.re
  have hW0 : 0 ≤ W := hΛ.trans hq.le
  have hnw : ‖w‖ ≤ W + 1 / 2 := norm_xiHeatFrequency_le_re q
  have hn1 : 0 < 1 + ‖w‖ := by positivity
  have hB1 : 1 ≤ 2 * C₀ * (1 + W) := by nlinarith
  have hlevel := exp_mul_pow_le_of_level (C := 2 * C₀) (M := 2 * k + 3) (by positivity) hη hΛ h1
    h2 hq.le
  have hpow1 : (C₀ * (1 + ‖w‖)) ^ j ≤ (2 * C₀ * (1 + W)) ^ j :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have hpow2 : (1 + ‖w‖) ^ (e + 1) ≤ (2 * C₀ * (1 + W)) ^ (e + 1) :=
    pow_le_pow_left₀ hn1.le (by nlinarith) _
  have hpow3 : (2 * C₀ * (1 + W)) ^ (j + (e + 1)) ≤ (2 * C₀ * (1 + W)) ^ (2 * k + 3) :=
    pow_le_pow_right₀ hB1 (by omega)
  have he := Real.exp_pos (-(a * W))
  rw [mul_one_div, le_div_iff₀ hn1]
  calc Real.exp (-(a * W)) * ((C₀ * (1 + ‖w‖)) ^ j * (1 + ‖w‖) ^ e) * (1 + ‖w‖)
      = Real.exp (-(a * W)) * ((C₀ * (1 + ‖w‖)) ^ j * (1 + ‖w‖) ^ (e + 1)) := by ring
    _ ≤ Real.exp (-(a * W)) * ((2 * C₀ * (1 + W)) ^ j * (2 * C₀ * (1 + W)) ^ (e + 1)) := by
        gcongr
    _ = Real.exp (-(a * W)) * (2 * C₀ * (1 + W)) ^ (j + (e + 1)) := by ring
    _ ≤ Real.exp (-(a * W)) * (2 * C₀ * (1 + W)) ^ (2 * k + 3) := by gcongr
    _ ≤ η := hlevel

/-! ## Real frequencies from Hardy's theorem -/

/-- The squared Hardy zeros are pairwise distinct real heat frequencies. -/
theorem hardyFrequency_injective :
    Function.Injective fun n : ℕ => (((hardyRealZero n) ^ 2 : ℝ) : ℂ) := by
  intro m n h
  have h' : hardyRealZero m ^ 2 = hardyRealZero n ^ 2 :=
    Complex.ofReal_inj.1 (show ((hardyRealZero m ^ 2 : ℝ) : ℂ) = ((hardyRealZero n ^ 2 : ℝ) : ℂ)
      from h)
  have hm := hardyRealZero_pos m
  have hn := hardyRealZero_pos n
  have : hardyRealZero m = hardyRealZero n := by nlinarith
  exact strictMono_hardyRealZero.injective this

theorem hardyFrequency_mem_heatFrequenciesBelow {n : ℕ} {Λ : ℝ}
    (hΛ : hardyRealZero n ^ 2 ≤ Λ) :
    (((hardyRealZero n) ^ 2 : ℝ) : ℂ) ∈ heatFrequenciesBelow Λ :=
  mem_heatFrequenciesBelow.2 ⟨hardyCopy n, xiHeatFrequency_hardyCopy n, by
    rw [Complex.ofReal_re]; exact hΛ⟩

/-- At least `d` heat frequencies lie below the square of the `d`-th Hardy zero. -/
theorem le_card_heatFrequenciesBelow {d : ℕ} {Λ : ℝ} (hΛ : hardyRealZero d ^ 2 ≤ Λ) :
    d ≤ (heatFrequenciesBelow Λ).card := by
  classical
  have hsub : (Finset.range d).image (fun n : ℕ => (((hardyRealZero n) ^ 2 : ℝ) : ℂ)) ⊆
      heatFrequenciesBelow Λ := by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hv
    refine hardyFrequency_mem_heatFrequenciesBelow (le_trans ?_ hΛ)
    have h1 := strictMono_hardyRealZero (Finset.mem_range.1 hn)
    have h0 := hardyRealZero_pos n
    nlinarith
  calc d = ((Finset.range d).image (fun n : ℕ => (((hardyRealZero n) ^ 2 : ℝ) : ℂ))).card := by
        rw [Finset.card_image_of_injective _ hardyFrequency_injective, Finset.card_range]
    _ ≤ _ := Finset.card_le_card hsub

/-- The root polynomial of the frequencies of real part `≤ Λ` other than `v`. -/
theorem norm_eval_heatRootPoly_erase_le {Λ d R : ℝ} {v w : ℂ} (hd : 0 < d) (hR : ‖v‖ ≤ R)
    (hsep : ∀ s ∈ heatFrequenciesBelow (2 * R + 2), s ≠ v → d ≤ ‖v - s‖) :
    ‖(heatRootPoly ((heatFrequenciesBelow Λ).erase v)).eval w‖ ≤
      ((2 + (2 * R + 3) / d) * (1 + ‖w‖)) ^ ((heatFrequenciesBelow Λ).erase v).card *
        ‖(heatRootPoly ((heatFrequenciesBelow Λ).erase v)).eval v‖ := by
  refine norm_eval_heatRootPoly_le fun s hs => norm_sub_le_of_far_or_sep hd hR fun hsR => ?_
  obtain ⟨hsv, hsB⟩ := Finset.mem_erase.1 hs
  obtain ⟨q, rfl, -⟩ := mem_heatFrequenciesBelow.1 hsB
  exact hsep _ (mem_heatFrequenciesBelow.2 ⟨q, rfl, (Complex.re_le_norm _).trans hsR.le⟩) hsv

/-! ## Nondegeneracy -/

/-- **Nondegeneracy of the heat Hankel form.**  If `H_a(P, R) = 0` for every polynomial `R`, then
`P = 0`. -/
theorem eq_zero_of_forall_heatHankel_eq_zero {a : ℝ} (ha : 0 < a) {P : ℂ[X]}
    (h : ∀ R : ℂ[X], heatHankel a P R = 0) : P = 0 := by
  classical
  by_contra hP
  -- a real frequency where `P` does not vanish
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P.eval (((hardyRealZero n) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hinf := Set.infinite_range_of_injective hardyFrequency_injective
    refine hinf ((Polynomial.finite_setOf_isRoot hP).subset ?_)
    rintro _ ⟨m, rfl⟩
    exact hall m
  set v : ℂ := (((hardyRealZero n) ^ 2 : ℝ) : ℂ)
  have hvconj : (starRingEnd ℂ) v = v := Complex.conj_ofReal _
  set R₀ := ‖v‖ with hR₀
  obtain ⟨d₀, hd₀, hdsep⟩ := exists_pos_le_norm_sub {v} (heatFrequenciesBelow (2 * R₀ + 2))
  have hsep : ∀ s ∈ heatFrequenciesBelow (2 * R₀ + 2), s ≠ v → d₀ ≤ ‖v - s‖ := fun s hs hsv =>
    hdsep v (Finset.mem_singleton_self v) s hs hsv (by rw [hvconj]; exact hsv)
  set C₀ := 2 + (2 * R₀ + 3) / d₀ with hC₀
  have hC₀1 : 1 ≤ C₀ := by
    have : 0 ≤ (2 * R₀ + 3) / d₀ := by positivity
    linarith
  set S₁ := ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖) with hS₁
  have hS₁0 : 0 ≤ S₁ := tsum_nonneg fun _ => by positivity
  set m₀ := polyMass P with hm₀
  have hm₀0 : 0 ≤ m₀ := polyMass_nonneg P
  have hPv : 0 < ‖P.eval v‖ := norm_pos_iff.2 hn
  set η := Real.exp (-(a * v.re)) * ‖P.eval v‖ / (2 * (m₀ + 1) * (S₁ + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨Λ, hΛU, hΛ0, k, hk, h1, h2⟩ := exists_heatLevel_at ha (by positivity : 0 < 2 * C₀) η
    (max v.re (hardyRealZero P.natDegree ^ 2))
  have hvΛ : v.re ≤ Λ := (le_max_left _ _).trans hΛU
  have hdk : P.natDegree ≤ k :=
    (le_card_heatFrequenciesBelow ((le_max_right _ _).trans hΛU)).trans hk
  set S := (heatFrequenciesBelow Λ).erase v with hS
  set K := heatRootPoly S with hK
  have hKv : K.eval v ≠ 0 := eval_heatRootPoly_ne_zero fun h => (Finset.mem_erase.1 h).1 rfl
  have hKv0 : 0 < ‖K.eval v‖ := norm_pos_iff.2 hKv
  have hcardS : S.card ≤ k := (Finset.card_erase_le).trans hk
  -- the pairing with `R = conjPoly K`
  have hpair := h (conjPoly K)
  have hterm : ∀ w : ℂ, heatHankelTermAt a P (conjPoly K) w =
      Complex.exp (-(a : ℂ) * w) * P.eval w * K.eval w := fun w => by
    rw [heatHankelTermAt, eval_conjPoly, Complex.conj_conj, Complex.conj_conj]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = Complex.exp (-(a : ℂ) * v) * P.eval v * K.eval v := ⟨_, rfl⟩
  -- the split of the terms
  obtain ⟨f, hf⟩ : ∃ f : XiZeroCopy → ℂ, ∀ q, f q = if xiHeatFrequency q = v then c else 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : XiZeroCopy → ℂ,
      ∀ q, g q = heatHankelTermAt a P (conjPoly K) (xiHeatFrequency q) - f q := ⟨_, fun _ => rfl⟩
  have hfin : {q : XiZeroCopy | xiHeatFrequency q = v}.Finite :=
    (finite_setOf_re_xiHeatFrequency_le v.re).subset fun q hq => by
      simp only [Set.mem_setOf_eq] at hq ⊢
      rw [hq]
  have hfsupp : ∀ q ∉ hfin.toFinset, f q = 0 := fun q hq => by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq
    rw [hf q, if_neg hq]
  have hfsum : ∑' q, f q = (hfin.toFinset.card : ℂ) * c := by
    rw [tsum_eq_sum hfsupp]
    have : ∀ q ∈ hfin.toFinset, f q = c := fun q hq => by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq
      rw [hf q, if_pos hq]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have hcard1 : 1 ≤ hfin.toFinset.card := by
    refine Finset.card_pos.2 ⟨hardyCopy n, ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, xiHeatFrequency_hardyCopy]
  have hsummf : Summable f := (hasSum_sum_of_ne_finset_zero hfsupp).summable
  have hsummT : Summable fun q => heatHankelTermAt a P (conjPoly K) (xiHeatFrequency q) :=
    summable_heatHankelTermAt ha P (conjPoly K)
  have hgeq : g = fun q => heatHankelTermAt a P (conjPoly K) (xiHeatFrequency q) - f q :=
    funext hg
  have hsummg : Summable g := hgeq ▸ hsummT.sub hsummf
  -- the terms of `g` vanish below the level and are small above it
  have hgweight : ∀ q, ‖g q‖ ≤ m₀ * ‖K.eval v‖ * (η * (1 / (1 + ‖xiHeatFrequency q‖))) := by
    intro q
    have hw0 : 0 ≤ m₀ * ‖K.eval v‖ * (η * (1 / (1 + ‖xiHeatFrequency q‖))) := by positivity
    by_cases hwv : xiHeatFrequency q = v
    · rw [hg q, hf q, if_pos hwv, hterm, hwv, ← hc, sub_self, norm_zero]
      rw [hwv] at hw0
      exact hw0
    · have hfq : f q = 0 := by rw [hf q, if_neg hwv]
      by_cases hlt : Λ < (xiHeatFrequency q).re
      · rw [hg q, hfq, sub_zero, hterm, norm_mul, norm_mul, Complex.norm_exp]
        have hre : (-(a : ℂ) * xiHeatFrequency q).re = -(a * (xiHeatFrequency q).re) := by simp
        rw [hre]
        have hP1 := norm_eval_le_polyMass P (xiHeatFrequency q)
        have hK1 := norm_eval_heatRootPoly_erase_le (Λ := Λ) (w := xiHeatFrequency q) hd₀ le_rfl
          hsep
        have he := (Real.exp_pos (-(a * (xiHeatFrequency q).re))).le
        have hweight := exp_mul_level_weight_le_of_exponent (j := S.card) (e := P.natDegree)
          hC₀1 hη0 hΛ0 (by omega) h1 h2 hlt
        calc Real.exp (-(a * (xiHeatFrequency q).re)) * ‖P.eval (xiHeatFrequency q)‖ *
              ‖K.eval (xiHeatFrequency q)‖
            ≤ Real.exp (-(a * (xiHeatFrequency q).re)) *
                (m₀ * (1 + ‖xiHeatFrequency q‖) ^ P.natDegree) *
                ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ S.card * ‖K.eval v‖) := by
              gcongr
          _ = m₀ * ‖K.eval v‖ * (Real.exp (-(a * (xiHeatFrequency q).re)) *
                ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ S.card *
                  (1 + ‖xiHeatFrequency q‖) ^ P.natDegree)) := by ring
          _ ≤ m₀ * ‖K.eval v‖ * (η * (1 / (1 + ‖xiHeatFrequency q‖))) :=
              mul_le_mul_of_nonneg_left hweight (by positivity)
      · have hmem : xiHeatFrequency q ∈ S := Finset.mem_erase.2 ⟨hwv,
          mem_heatFrequenciesBelow.2 ⟨q, rfl, not_lt.1 hlt⟩⟩
        have hK0 : K.eval (xiHeatFrequency q) = 0 := eval_heatRootPoly_eq_zero hmem
        rw [hg q, hfq, sub_zero, hterm, hK0, mul_zero, norm_zero]
        exact hw0
  have hgsum : ‖∑' q, g q‖ ≤ m₀ * ‖K.eval v‖ * (η * S₁) := by
    calc ‖∑' q, g q‖ ≤ ∑' q, ‖g q‖ := norm_tsum_le_tsum_norm hsummg.norm
      _ ≤ ∑' q, m₀ * ‖K.eval v‖ * (η * (1 / (1 + ‖xiHeatFrequency q‖))) :=
          Summable.tsum_le_tsum hgweight hsummg.norm
            ((summable_inv_one_add_norm_xiHeatFrequency.mul_left η).mul_left _)
      _ = m₀ * ‖K.eval v‖ * (η * S₁) := by rw [tsum_mul_left, tsum_mul_left]
  -- `0 = Σ f + Σ g`
  have hsplit : heatHankel a P (conjPoly K) = ∑' q, f q + ∑' q, g q := by
    rw [← hsummf.tsum_add hsummg]
    exact tsum_congr fun q => by rw [hg q]; ring
  rw [hpair, hfsum] at hsplit
  have hnc : ‖c‖ = Real.exp (-(a * v.re)) * ‖P.eval v‖ * ‖K.eval v‖ := by
    rw [hc, norm_mul, norm_mul, Complex.norm_exp]
    congr 2
    simp
  have hmain : ‖c‖ ≤ ‖(hfin.toFinset.card : ℂ) * c‖ := by
    rw [norm_mul, Complex.norm_natCast]
    exact le_mul_of_one_le_left (norm_nonneg _) (by exact_mod_cast hcard1)
  have heq : ‖(hfin.toFinset.card : ℂ) * c‖ = ‖∑' q, g q‖ := by
    have : (hfin.toFinset.card : ℂ) * c = -∑' q, g q := by linear_combination -hsplit
    rw [this, norm_neg]
  have hηval : η * (2 * (m₀ + 1) * (S₁ + 1)) = Real.exp (-(a * v.re)) * ‖P.eval v‖ := by
    rw [hη]
    field_simp
  have hηS : m₀ * (η * S₁) < Real.exp (-(a * v.re)) * ‖P.eval v‖ := by
    rw [← hηval]
    nlinarith [mul_nonneg hm₀0 hS₁0, mul_nonneg hη0.le hS₁0, mul_nonneg hm₀0 hη0.le]
  have hfinal := hmain.trans (heq.le.trans hgsum)
  rw [hnc] at hfinal
  nlinarith [mul_lt_mul_of_pos_right hηS hKv0]

/-! ## Infinite positive index -/

theorem hardyRealZero_sq_le_of_lt {i n : ℕ} (h : i < n) :
    hardyRealZero i ^ 2 ≤ hardyRealZero n ^ 2 := by
  have h1 := strictMono_hardyRealZero h
  have h0 := hardyRealZero_pos i
  nlinarith

/-- **Infinite positive index.**  For every `n` there is an `n`-dimensional subspace of `ℂ[X]` on
which `Re H_a` is positive definite, unconditionally. -/
theorem exists_heatHankel_pos_subspace {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∃ V : Submodule ℂ ℂ[X], Module.finrank ℂ V = n ∧
      ∀ P ∈ V, P ≠ 0 → 0 < (heatHankel a P P).re := by
  classical
  -- the real frequencies and their bound
  set v : Fin n → ℂ := fun i => (((hardyRealZero i) ^ 2 : ℝ) : ℂ) with hvdef
  have hvinj : Function.Injective v := fun i j h =>
    Fin.ext (hardyFrequency_injective h)
  have hvconj : ∀ i, (starRingEnd ℂ) (v i) = v i := fun i => Complex.conj_ofReal _
  set R₀ := hardyRealZero n ^ 2 with hR₀
  have hR₀0 : 0 ≤ R₀ := sq_nonneg _
  have hvR : ∀ i, ‖v i‖ ≤ R₀ := fun i => by
    rw [hvdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hardyRealZero_sq_le_of_lt i.2
  have hvre : ∀ i, (v i).re = hardyRealZero i ^ 2 := fun i => Complex.ofReal_re _
  set G := Finset.univ.image v with hG
  obtain ⟨d₀, hd₀, hdsep⟩ := exists_pos_le_norm_sub G (heatFrequenciesBelow (2 * R₀ + 2))
  have hsep : ∀ i, ∀ s ∈ heatFrequenciesBelow (2 * R₀ + 2), s ≠ v i → d₀ ≤ ‖v i - s‖ :=
    fun i s hs hsv => hdsep (v i) (Finset.mem_image_of_mem v (Finset.mem_univ i)) s hs hsv
      (by rw [hvconj]; exact hsv)
  set C₀ := 2 + (2 * R₀ + 3) / d₀ with hC₀
  have hC₀1 : 1 ≤ C₀ := by
    have : 0 ≤ (2 * R₀ + 3) / d₀ := by positivity
    linarith
  set S₁ := ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖) with hS₁
  have hS₁0 : 0 ≤ S₁ := tsum_nonneg fun _ => by positivity
  set η := Real.exp (-(a * R₀)) / (2 * (n + 1) * (S₁ + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨Λ, hΛR, hΛ0, k, hk, h1, h2⟩ := exists_heatLevel_at ha (by positivity : 0 < 2 * C₀) η R₀
  have hvΛ : ∀ i, v i ∈ heatFrequenciesBelow Λ := fun i =>
    mem_heatFrequenciesBelow.2 ⟨hardyCopy i, xiHeatFrequency_hardyCopy i, by
      rw [hvre]; exact (hardyRealZero_sq_le_of_lt i.2).trans hΛR⟩
  -- the normalized root polynomials
  set K : Fin n → ℂ[X] := fun i => heatRootPoly ((heatFrequenciesBelow Λ).erase (v i)) with hK
  have hKv : ∀ i, (K i).eval (v i) ≠ 0 := fun i =>
    eval_heatRootPoly_ne_zero fun h => (Finset.mem_erase.1 h).1 rfl
  set P : Fin n → ℂ[X] := fun i => C ((K i).eval (v i))⁻¹ * K i with hP
  have hPv : ∀ i j, (P i).eval (v j) = if i = j then 1 else 0 := by
    intro i j
    simp only [hP, eval_mul, eval_C]
    split_ifs with hij
    · subst hij
      exact inv_mul_cancel₀ (hKv i)
    · have hmem : v j ∈ (heatFrequenciesBelow Λ).erase (v i) :=
        Finset.mem_erase.2 ⟨fun h => hij (hvinj h).symm, hvΛ j⟩
      rw [hK]
      simp only
      rw [eval_heatRootPoly_eq_zero hmem, mul_zero]
  have hPlow : ∀ i, ∀ q : XiZeroCopy, (xiHeatFrequency q).re ≤ Λ →
      (∀ j, xiHeatFrequency q ≠ v j) → (P i).eval (xiHeatFrequency q) = 0 := by
    intro i q hq hne
    have hmem : xiHeatFrequency q ∈ (heatFrequenciesBelow Λ).erase (v i) :=
      Finset.mem_erase.2 ⟨hne i, mem_heatFrequenciesBelow.2 ⟨q, rfl, hq⟩⟩
    simp only [hP, hK, eval_mul, eval_C, eval_heatRootPoly_eq_zero hmem, mul_zero]
  have hPbound : ∀ i, ∀ z : ℂ, ‖(P i).eval z‖ ≤ (C₀ * (1 + ‖z‖)) ^ k := by
    intro i z
    have hb := norm_eval_heatRootPoly_erase_le (Λ := Λ) (w := z) hd₀ (hvR i) (hsep i)
    have hKv0 := norm_pos_iff.2 (hKv i)
    have hcard : ((heatFrequenciesBelow Λ).erase (v i)).card ≤ k :=
      (Finset.card_erase_le).trans hk
    have hbase : 1 ≤ C₀ * (1 + ‖z‖) := by nlinarith [norm_nonneg z]
    simp only [hP, eval_mul, eval_C, norm_mul, norm_inv]
    calc ‖(K i).eval (v i)‖⁻¹ * ‖(K i).eval z‖
        ≤ ‖(K i).eval (v i)‖⁻¹ * ((C₀ * (1 + ‖z‖)) ^ ((heatFrequenciesBelow Λ).erase (v i)).card *
            ‖(K i).eval (v i)‖) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (C₀ * (1 + ‖z‖)) ^ ((heatFrequenciesBelow Λ).erase (v i)).card := by
          field_simp
      _ ≤ (C₀ * (1 + ‖z‖)) ^ k := pow_le_pow_right₀ hbase hcard
  -- the linear combinations
  set Φ : (Fin n → ℂ) →ₗ[ℂ] ℂ[X] := Fintype.linearCombination ℂ P with hΦ
  have hΦapp : ∀ x, Φ x = ∑ i, x i • P i := fun x => Fintype.linearCombination_apply ℂ P x
  have hFeval : ∀ x z, (Φ x).eval z = ∑ i, x i * (P i).eval z := fun x z => by
    rw [hΦapp, eval_finsetSum]
    simp [eval_smul, smul_eq_mul]
  have hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (heatHankel a (Φ x) (Φ x)).re := by
    intro x hx
    set F := Φ x with hF
    set X2 := ∑ i, ‖x i‖ ^ 2 with hX2
    have hX2pos : 0 < X2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
      have : 0 < ‖x i‖ ^ 2 := by positivity
      exact lt_of_lt_of_le this (Finset.single_le_sum (fun j _ => sq_nonneg ‖x j‖)
        (Finset.mem_univ i))
    have hFv : ∀ j, F.eval (v j) = x j := fun j => by
      rw [hF, hFeval, Finset.sum_eq_single j (fun i _ hij => by rw [hPv i j, if_neg hij,
        mul_zero]) (by simp)]
      rw [hPv j j, if_pos rfl, mul_one]
    have hFbound : ∀ z, ‖F.eval z‖ ^ 2 ≤ n * X2 * ((C₀ * (1 + ‖z‖)) ^ k) ^ 2 := fun z => by
      have hs : ‖F.eval z‖ ≤ (∑ i, ‖x i‖) * (C₀ * (1 + ‖z‖)) ^ k := by
        rw [hF, hFeval, Finset.sum_mul]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hPbound i z) (norm_nonneg _)
      have hcs : (∑ i, ‖x i‖) ^ 2 ≤ n * X2 := by
        have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => ‖x i‖)
        simpa [hX2] using this
      have hs0 : 0 ≤ (∑ i, ‖x i‖) * (C₀ * (1 + ‖z‖)) ^ k := by positivity
      calc ‖F.eval z‖ ^ 2 ≤ ((∑ i, ‖x i‖) * (C₀ * (1 + ‖z‖)) ^ k) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hs 2
        _ = (∑ i, ‖x i‖) ^ 2 * ((C₀ * (1 + ‖z‖)) ^ k) ^ 2 := by ring
        _ ≤ n * X2 * ((C₀ * (1 + ‖z‖)) ^ k) ^ 2 := by gcongr
    -- termwise lower bound
    set hfun : XiZeroCopy → ℝ := fun q => ∑ j, (if xiHeatFrequency q = v j then
      Real.exp (-(a * (v j).re)) * ‖x j‖ ^ 2 else 0) with hhfun
    set tfun : XiZeroCopy → ℝ := fun q => (if Λ < (xiHeatFrequency q).re then
      n * X2 * (η * (1 / (1 + ‖xiHeatFrequency q‖))) else 0) with htfun
    have hterm : ∀ q, hfun q - tfun q ≤ (heatHankelTermAt a F F (xiHeatFrequency q)).re := by
      intro q
      set w := xiHeatFrequency q with hw
      by_cases hhit : ∃ j, w = v j
      · obtain ⟨j, hj⟩ := hhit
        have hh : hfun q = Real.exp (-(a * (v j).re)) * ‖x j‖ ^ 2 := by
          simp only [hhfun]
          rw [Finset.sum_eq_single j (fun i _ hij => by
            rw [if_neg (fun h => hij (hvinj (h.symm.trans hj)))]) (by simp), if_pos hj]
        have ht : tfun q = 0 := by
          simp only [htfun]
          rw [if_neg]
          rw [not_lt, ← hw, hj, hvre]
          exact (hardyRealZero_sq_le_of_lt j.2).trans hΛR
        rw [hh, ht, sub_zero, hj, heatHankelTermAt, hvconj, hFv]
        have hre : (Complex.exp (-(a : ℂ) * v j) * x j * (starRingEnd ℂ) (x j)).re =
            Real.exp (-(a * (v j).re)) * ‖x j‖ ^ 2 := by
          have hexp : Complex.exp (-(a : ℂ) * v j) = ((Real.exp (-(a * (v j).re)) : ℝ) : ℂ) := by
            rw [hvre j, Complex.ofReal_exp]
            congr 1
            simp only [hvdef]
            push_cast
            ring
          rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hexp,
            ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [hre]
      · push Not at hhit
        have hh : hfun q = 0 := by
          simp only [hhfun]
          exact Finset.sum_eq_zero fun j _ => if_neg (hhit j)
        rw [hh, zero_sub]
        by_cases hlt : Λ < w.re
        · have ht : tfun q = n * X2 * (η * (1 / (1 + ‖w‖))) := by
            simp only [htfun]; rw [if_pos hlt]
          rw [ht]
          have hnorm : ‖heatHankelTermAt a F F w‖ ≤ n * X2 * (η * (1 / (1 + ‖w‖))) := by
            rw [heatHankelTermAt, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_conj]
            have hre : (-(a : ℂ) * w).re = -(a * w.re) := by simp
            rw [hre]
            have hb1 := hFbound w
            have hb2 := hFbound ((starRingEnd ℂ) w)
            rw [Complex.norm_conj] at hb2
            have hprod : ‖F.eval w‖ * ‖F.eval ((starRingEnd ℂ) w)‖ ≤
                n * X2 * ((C₀ * (1 + ‖w‖)) ^ k) ^ 2 := by
              nlinarith [sq_nonneg (‖F.eval w‖ - ‖F.eval ((starRingEnd ℂ) w)‖),
                norm_nonneg (F.eval w), norm_nonneg (F.eval ((starRingEnd ℂ) w))]
            have hweight := exp_mul_level_weight_le_of_exponent (j := 2 * k) (e := 0) hC₀1 hη0 hΛ0
              (by omega) h1 h2 hlt
            rw [pow_zero, mul_one] at hweight
            have he := (Real.exp_pos (-(a * w.re))).le
            have hnX : 0 ≤ (n : ℝ) * X2 := by positivity
            calc Real.exp (-(a * w.re)) * ‖F.eval w‖ * ‖F.eval ((starRingEnd ℂ) w)‖
                = Real.exp (-(a * w.re)) * (‖F.eval w‖ * ‖F.eval ((starRingEnd ℂ) w)‖) := by
                  ring
              _ ≤ Real.exp (-(a * w.re)) * (n * X2 * ((C₀ * (1 + ‖w‖)) ^ k) ^ 2) :=
                  mul_le_mul_of_nonneg_left hprod he
              _ = n * X2 * (Real.exp (-(a * w.re)) * (C₀ * (1 + ‖w‖)) ^ (2 * k)) := by ring
              _ ≤ n * X2 * (η * (1 / (1 + ‖w‖))) := mul_le_mul_of_nonneg_left hweight hnX
          have := Complex.abs_re_le_norm (heatHankelTermAt a F F w)
          have := neg_abs_le (heatHankelTermAt a F F w).re
          linarith
        · have ht : tfun q = 0 := by simp only [htfun]; rw [if_neg hlt]
          have hFw : F.eval w = 0 := by
            rw [hF, hFeval]
            exact Finset.sum_eq_zero fun i _ => by
              rw [hPlow i q (not_lt.1 hlt) hhit, mul_zero]
          rw [ht, neg_zero, heatHankelTermAt, hFw, mul_zero, zero_mul, Complex.zero_re]
    -- summation
    have hsummT : Summable fun q => (heatHankelTermAt a F F (xiHeatFrequency q)).re :=
      (summable_heatHankelTermAt ha F F).mapL Complex.reCLM
    have hsummj : ∀ j, Summable fun q : XiZeroCopy => (if xiHeatFrequency q = v j then
        Real.exp (-(a * (v j).re)) * ‖x j‖ ^ 2 else 0) := by
      intro j
      have hfin : {q : XiZeroCopy | xiHeatFrequency q = v j}.Finite :=
        (finite_setOf_re_xiHeatFrequency_le (v j).re).subset fun q hq => by
          simp only [Set.mem_setOf_eq] at hq ⊢
          rw [hq]
      refine (hasSum_sum_of_ne_finset_zero (s := hfin.toFinset) fun q hq => ?_).summable
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq
      rw [if_neg hq]
    have hsummh : Summable hfun := summable_sum fun j _ => hsummj j
    have hsummt : Summable tfun := by
      refine ((summable_inv_one_add_norm_xiHeatFrequency.mul_left (n * X2 * η))).of_nonneg_of_le
        (fun q => by simp only [htfun]; split_ifs <;> positivity) fun q => ?_
      simp only [htfun]
      split_ifs
      · exact le_of_eq (by ring)
      · positivity
    have hlow : ∑' q, (hfun q - tfun q) ≤ (heatHankel a F F).re := by
      rw [heatHankel, Complex.re_tsum (summable_heatHankelTermAt ha F F)]
      exact Summable.tsum_le_tsum hterm (hsummh.sub hsummt) hsummT
    have hh_ge : ∑ j, Real.exp (-(a * (v j).re)) * ‖x j‖ ^ 2 ≤ ∑' q, hfun q := by
      rw [show (∑' q, hfun q) = ∑ j, ∑' q : XiZeroCopy, (if xiHeatFrequency q = v j then
          Real.exp (-(a * (v j).re)) * ‖x j‖ ^ 2 else 0) from
        Summable.tsum_finsetSum fun j _ => hsummj j]
      refine Finset.sum_le_sum fun j _ => ?_
      have hle := (hsummj j).le_tsum (hardyCopy j) (fun q _ => by split_ifs <;> positivity)
      rw [if_pos (by rw [xiHeatFrequency_hardyCopy])] at hle
      exact hle
    have ht_le : ∑' q, tfun q ≤ n * X2 * (η * S₁) := by
      calc ∑' q, tfun q ≤ ∑' q, n * X2 * (η * (1 / (1 + ‖xiHeatFrequency q‖))) :=
            Summable.tsum_le_tsum (fun q => by
              simp only [htfun]; split_ifs
              · exact le_rfl
              · positivity) hsummt
              ((summable_inv_one_add_norm_xiHeatFrequency.mul_left η).mul_left _)
        _ = n * X2 * (η * S₁) := by rw [tsum_mul_left, tsum_mul_left]
    have hexpR : ∀ j, Real.exp (-(a * R₀)) ≤ Real.exp (-(a * (v j).re)) := fun j => by
      refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ ha.le))
      exact (Complex.re_le_norm _).trans (hvR j)
    have hmainX : Real.exp (-(a * R₀)) * X2 ≤ ∑ j, Real.exp (-(a * (v j).re)) * ‖x j‖ ^ 2 := by
      rw [hX2, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hexpR j) (sq_nonneg _)
    have hηval : η * (2 * (n + 1) * (S₁ + 1)) = Real.exp (-(a * R₀)) := by
      rw [hη]; field_simp
    have hsmall : n * X2 * (η * S₁) < Real.exp (-(a * R₀)) * X2 := by
      have hE := Real.exp_pos (-(a * R₀))
      have : (n : ℝ) * (η * S₁) < Real.exp (-(a * R₀)) := by
        rw [← hηval]
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith [mul_nonneg hn0 (mul_nonneg hη0.le hS₁0), mul_nonneg hη0.le hS₁0]
      nlinarith
    have hsub : ∑' q, (hfun q - tfun q) = ∑' q, hfun q - ∑' q, tfun q :=
      hsummh.tsum_sub hsummt
    linarith
  -- the subspace
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have := hpos x hne
    rw [hx] at this
    simp [heatHankel, heatHankelTermAt] at this
  refine ⟨LinearMap.range Φ, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  · rintro F ⟨x, rfl⟩ hF0
    have hx : x ≠ 0 := by
      rintro rfl
      exact hF0 (map_zero Φ)
    exact hpos x hx

end

end RHTower
