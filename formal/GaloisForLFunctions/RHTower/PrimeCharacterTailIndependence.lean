import GaloisForLFunctions.RHTower.Sieve.RouteTFixedShortIntervalPrimeSupply
import GaloisForLFunctions.HTGeometry.ExpSumVanishing

/-!
# Prime characters are independent modulo finite prime support

Prime logarithms are eventually dense on the line: the unconditional fixed-exponent short-interval
prime supply puts one in every window of any prescribed length once the window is far enough out.
An exponential sum with distinct real frequencies is Lipschitz, so vanishing along prime
logarithms forces vanishing on the whole line, and the corpus exponential-sum uniqueness theorem
then kills every coefficient.

Renormalizing a finite combination of prime characters `p ↦ p^{-x}` by the smallest real part
exposes exactly one such exponential sum.  Hence distinct prime characters are linearly independent
modulo finite prime support.
-/

namespace RHTower

open Filter Real
open scoped Topology BigOperators

/-- **Eventual density of prime logarithms.**  The unconditional fixed-exponent short-interval
prime supply puts a prime logarithm in every window `(t, t + δ]` once `t` is large. -/
theorem exists_prime_log_in_window {δ : ℝ} (hδ : 0 < δ) :
    ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t →
      ∃ p : ℕ, p.Prime ∧ t < Real.log p ∧ Real.log p ≤ t + δ := by
  obtain ⟨X₀, hX₀, hsupply⟩ := RHTower.Sieve.exists_threshold_routeT_prime_in_fixed_window
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℝ, ∀ t : ℝ, T₁ ≤ t → Real.exp (-(29 / 100 : ℝ) * t) ≤ δ := by
    have hlim : Tendsto (fun t : ℝ => Real.exp (-(29 / 100 : ℝ) * t)) atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ => -(29 / 100 : ℝ) * t) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by norm_num)
      exact Real.tendsto_exp_atBot.comp this
    obtain ⟨T₁, hT₁⟩ := (hlim.eventually (eventually_le_nhds hδ)).exists_forall_of_atTop
    exact ⟨T₁, fun t ht => hT₁ t ht⟩
  refine ⟨max (Real.log X₀ + 1) (max T₁ 0), fun t ht => ?_⟩
  have htX : X₀ ≤ Real.exp t := by
    have h1 : Real.log X₀ + 1 ≤ t := le_trans (le_max_left _ _) ht
    have := Real.exp_le_exp.mpr (show Real.log X₀ ≤ t by linarith)
    calc X₀ = Real.exp (Real.log X₀) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp t := this
  obtain ⟨p, hp, hlt, hle⟩ := hsupply (Real.exp t) htX
  refine ⟨p, hp, ?_, ?_⟩
  · rw [show t = Real.log (Real.exp t) from (Real.log_exp t).symm]
    exact Real.log_lt_log (Real.exp_pos t) hlt
  · have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hbound : (p : ℝ) ≤ Real.exp t * (1 + Real.exp (-(29 / 100 : ℝ) * t)) := by
      have hpow : (Real.exp t) ^ RHTower.Sieve.routeTHoheiselEveryBaseExponent
          = Real.exp t * Real.exp (-(29 / 100 : ℝ) * t) := by
        rw [← Real.exp_log (Real.exp_pos t), Real.log_exp]
        rw [← Real.exp_mul, ← Real.exp_add]
        · congr 1
          rw [RHTower.Sieve.routeTHoheiselEveryBaseExponent]
          ring
      calc (p : ℝ) ≤ Real.exp t + (Real.exp t) ^ RHTower.Sieve.routeTHoheiselEveryBaseExponent :=
            hle
        _ = Real.exp t * (1 + Real.exp (-(29 / 100 : ℝ) * t)) := by rw [hpow]; ring
    have hlog : Real.log p ≤ t + Real.log (1 + Real.exp (-(29 / 100 : ℝ) * t)) := by
      have h := Real.log_le_log hppos hbound
      rwa [Real.log_mul (Real.exp_ne_zero t) (by positivity), Real.log_exp] at h
    have hsmall : Real.log (1 + Real.exp (-(29 / 100 : ℝ) * t)) ≤ δ := by
      refine le_trans (Real.log_le_sub_one_of_pos (by positivity)) ?_
      have : Real.exp (-(29 / 100 : ℝ) * t) ≤ δ :=
        hT₁ t (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht)
      linarith
    linarith

/-! ## Exponential sums with real frequencies -/

/-- A finite exponential sum with real frequencies, indexed by a finite set. -/
noncomputable def expSumOn {ι : Type*} (J : Finset ι) (c : ι → ℂ) (θ : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ j ∈ J, c j * HTGeometry.cis (θ j) t

theorem hasDerivAt_cis (l t : ℝ) :
    HasDerivAt (fun u : ℝ => HTGeometry.cis l u)
      (HTGeometry.cis l t * (Complex.I * (l : ℂ))) t := by
  have h0 : HasDerivAt (fun u : ℝ => l * u) l t := by
    simpa using (hasDerivAt_id t).const_mul l
  have h1 : HasDerivAt (fun u : ℝ => ((l * u : ℝ) : ℂ)) ((l : ℝ) : ℂ) t := h0.ofReal_comp
  simpa [HTGeometry.cis, Complex.ofReal_mul] using (h1.const_mul Complex.I).cexp

theorem hasDerivAt_expSumOn {ι : Type*} (J : Finset ι) (c : ι → ℂ) (θ : ι → ℝ) (t : ℝ) :
    HasDerivAt (expSumOn J c θ)
      (∑ j ∈ J, c j * (HTGeometry.cis (θ j) t * (Complex.I * (θ j : ℂ)))) t := by
  classical
  simpa only [expSumOn] using!
    HasDerivAt.fun_sum (fun j _ => (hasDerivAt_cis (θ j) t).const_mul (c j))

/-- The Lipschitz constant of an exponential sum. -/
noncomputable def expSumLip {ι : Type*} (J : Finset ι) (c : ι → ℂ) (θ : ι → ℝ) : ℝ :=
  ∑ j ∈ J, ‖c j‖ * |θ j|

theorem expSumLip_nonneg {ι : Type*} (J : Finset ι) (c : ι → ℂ) (θ : ι → ℝ) :
    0 ≤ expSumLip J c θ :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)

theorem norm_deriv_expSumOn_le {ι : Type*} (J : Finset ι) (c : ι → ℂ) (θ : ι → ℝ) (t : ℝ) :
    ‖deriv (expSumOn J c θ) t‖ ≤ expSumLip J c θ := by
  classical
  rw [(hasDerivAt_expSumOn J c θ t).deriv]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_mul, norm_mul, norm_mul, HTGeometry.norm_cis, Complex.norm_I]
  simp

theorem norm_expSumOn_sub_le {ι : Type*} (J : Finset ι) (c : ι → ℂ) (θ : ι → ℝ) (s t : ℝ) :
    ‖expSumOn J c θ t - expSumOn J c θ s‖ ≤ expSumLip J c θ * |t - s| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := expSumOn J c θ) (s := Set.univ) (C := expSumLip J c θ)
    (fun x _ => (hasDerivAt_expSumOn J c θ x).differentiableAt)
    (fun x _ => norm_deriv_expSumOn_le J c θ x) convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa [Real.norm_eq_abs] using this

/-! ## Vanishing along prime logarithms -/

theorem tendsto_expSumOn_atTop_zero_of_prime_log {ι : Type*}
    (J : Finset ι) (c : ι → ℂ) (θ : ι → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      ‖expSumOn J c θ (Real.log p)‖ ≤ ε) :
    Tendsto (expSumOn J c θ) atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  set M := expSumLip J c θ with hM
  have hMnn : 0 ≤ M := expSumLip_nonneg J c θ
  set δ := ε / (4 * (M + 1)) with hδdef
  have hδ : 0 < δ := by
    apply div_pos hε
    linarith
  obtain ⟨T₀, hT₀⟩ := exists_prime_log_in_window hδ
  obtain ⟨P, hP⟩ := h (ε / 4) (by linarith)
  filter_upwards [eventually_ge_atTop (max T₀ (Real.log (P + 1)))] with t ht
  obtain ⟨p, hp, hlt, hle⟩ := hT₀ t (le_trans (le_max_left _ _) ht)
  have hPle : P ≤ p := by
    have hlog : Real.log (P + 1) < Real.log p :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) ht) hlt
    have hPpos : (0 : ℝ) < (P : ℝ) + 1 := by positivity
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have := (Real.log_lt_log_iff hPpos hppos).mp hlog
    have hlt' : (P : ℝ) < (p : ℝ) := by linarith
    exact_mod_cast hlt'.le
  have h1 : ‖expSumOn J c θ (Real.log p)‖ ≤ ε / 4 := hP p hp hPle
  have h2 : ‖expSumOn J c θ t - expSumOn J c θ (Real.log p)‖ ≤ M * δ := by
    refine le_trans (norm_expSumOn_sub_le J c θ (Real.log p) t) ?_
    have habs : |t - Real.log p| ≤ δ := by
      rw [abs_le]
      constructor <;> linarith
    exact mul_le_mul_of_nonneg_left habs hMnn
  have h3 : M * δ ≤ ε / 4 := by
    rw [hδdef]
    have hpos : (0 : ℝ) < 4 * (M + 1) := by linarith
    rw [mul_div_assoc', div_le_iff₀ hpos]
    nlinarith
  calc ‖expSumOn J c θ t‖
      ≤ ‖expSumOn J c θ t - expSumOn J c θ (Real.log p)‖ +
        ‖expSumOn J c θ (Real.log p)‖ := by
        simpa using norm_add_le (expSumOn J c θ t - expSumOn J c θ (Real.log p))
          (expSumOn J c θ (Real.log p))
    _ ≤ ε / 4 + ε / 4 := add_le_add (le_trans h2 h3) h1
    _ < ε := by linarith

/-! ## Independence of prime characters modulo finite support -/

theorem natCast_cpow_imaginary {p : ℕ} (hp : 0 < p) (u : ℝ) :
    (p : ℂ) ^ (((u : ℝ) : ℂ) * Complex.I) = HTGeometry.cis u (Real.log p) := by
  have hne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.natCast_log, HTGeometry.cis]
  congr 1
  push_cast
  ring

/-- **Prime-character independence modulo finite support.**  A finite complex linear combination of
the characters `p ↦ p^{-x}` with distinct exponents which vanishes at every sufficiently large
prime has all coefficients zero.  After renormalizing by the smallest real part, only one layer
survives; it is a trigonometric polynomial in `log p`, and prime logarithms are eventually
dense. -/
theorem primeCharacter_coeff_eq_zero_of_eventually_vanishing
    {ι : Type*} [DecidableEq ι] (c : ι → ℂ) (x : ι → ℂ) :
    ∀ J : Finset ι,
      (∀ i ∈ J, ∀ j ∈ J, x i = x j → i = j) →
      (∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
        ∑ j ∈ J, c j * (p : ℂ) ^ (-(x j)) = 0) →
      ∀ j ∈ J, c j = 0 := by
  classical
  refine Finset.strongInduction ?_
  intro J ih hinj hvanish
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · simp
  obtain ⟨j₀, hj₀J, hj₀min⟩ := J.exists_min_image (fun j => (x j).re) hJ
  set a := (x j₀).re with ha
  set K := J.filter (fun j => (x j).re = a) with hK
  set L := J.filter (fun j => ¬ (x j).re = a) with hL
  have hKsub : K ⊆ J := Finset.filter_subset _ _
  have hLsub : L ⊆ J := Finset.filter_subset _ _
  have hj₀K : j₀ ∈ K := Finset.mem_filter.mpr ⟨hj₀J, rfl⟩
  obtain ⟨P, hP⟩ := hvanish
  set θ : ι → ℝ := fun j => -(x j).im with hθ
  have hθinj : ∀ i ∈ K, ∀ j ∈ K, θ i = θ j → i = j := by
    intro i hi j hj hij
    have hire : (x i).re = a := (Finset.mem_filter.mp hi).2
    have hjre : (x j).re = a := (Finset.mem_filter.mp hj).2
    refine hinj i (hKsub hi) j (hKsub hj) (Complex.ext ?_ ?_)
    · rw [hire, hjre]
    · have h2 : -(x i).im = -(x j).im := hij
      linarith
  have hlayer : ∀ p : ℕ, p.Prime → P ≤ p →
      expSumOn K c θ (Real.log p) = -∑ j ∈ L, c j * (p : ℂ) ^ ((a : ℂ) - x j) := by
    intro p hp hPp
    have hppos : 0 < p := hp.pos
    have hne : (p : ℂ) ≠ 0 := by exact_mod_cast hppos.ne'
    have hshift : ∀ j : ι, c j * (p : ℂ) ^ ((a : ℂ) - x j)
        = (p : ℂ) ^ (a : ℂ) * (c j * (p : ℂ) ^ (-(x j))) := by
      intro j
      rw [show (a : ℂ) - x j = (a : ℂ) + -(x j) by ring, Complex.cpow_add _ _ hne]
      ring
    have htotal : ∑ j ∈ J, c j * (p : ℂ) ^ ((a : ℂ) - x j) = 0 := by
      simp only [hshift]
      rw [← Finset.mul_sum, hP p hp hPp, mul_zero]
    have hsplit := Finset.sum_filter_add_sum_filter_not J (fun j => (x j).re = a)
      (fun j => c j * (p : ℂ) ^ ((a : ℂ) - x j))
    have hKterm : ∑ j ∈ K, c j * (p : ℂ) ^ ((a : ℂ) - x j) = expSumOn K c θ (Real.log p) := by
      rw [expSumOn]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hre : (x j).re = a := (Finset.mem_filter.mp hj).2
      have hxj : (a : ℂ) - x j = ((θ j : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hre, hθ]
      rw [hxj, natCast_cpow_imaginary hppos (θ j)]
    rw [hK, hL] at *
    rw [hKterm] at hsplit
    rw [htotal] at hsplit
    linear_combination hsplit
  have htailbound : ∀ p : ℕ, p.Prime → P ≤ p →
      ‖expSumOn K c θ (Real.log p)‖ ≤ ∑ j ∈ L, ‖c j‖ * (p : ℝ) ^ (a - (x j).re) := by
    intro p hp hPp
    rw [hlayer p hp hPp, norm_neg]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos]
    simp
  have hLtend : Tendsto
      (fun p : ℕ => ∑ j ∈ L, ‖c j‖ * (p : ℝ) ^ (a - (x j).re)) atTop (𝓝 0) := by
    have : Tendsto (fun p : ℕ => ∑ j ∈ L, ‖c j‖ * (p : ℝ) ^ (a - (x j).re)) atTop
        (𝓝 (∑ j ∈ L, (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun j hj => ?_
      have hneg : a - (x j).re < 0 := by
        have hjJ := hLsub hj
        have hne : ¬ (x j).re = a := (Finset.mem_filter.mp hj).2
        have hge : a ≤ (x j).re := hj₀min j hjJ
        rcases lt_or_eq_of_le hge with h1 | h1
        · linarith
        · exact absurd h1.symm hne
      have hbase : Tendsto (fun y : ℝ => y ^ (a - (x j).re)) atTop (𝓝 0) := by
        have := tendsto_rpow_neg_atTop (y := (x j).re - a) (by linarith)
        simpa [neg_sub] using this
      have := (hbase.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul ‖c j‖
      simpa using this
    simpa using this
  have hGp : ∀ ε : ℝ, 0 < ε → ∃ P' : ℕ, ∀ p : ℕ, p.Prime → P' ≤ p →
      ‖expSumOn K c θ (Real.log p)‖ ≤ ε := by
    intro ε hε
    obtain ⟨P₁, hP₁⟩ := (Filter.eventually_atTop.1
      ((hLtend.eventually (eventually_le_nhds hε))))
    refine ⟨max P P₁, fun p hp hPp => ?_⟩
    refine le_trans (htailbound p hp (le_trans (le_max_left _ _) hPp)) ?_
    exact hP₁ p (le_trans (le_max_right _ _) hPp)
  have hKzero : ∀ j ∈ K, c j = 0 := by
    intro j hj
    have hzero := tendsto_expSumOn_atTop_zero_of_prime_log K c θ hGp
    -- transport to the corpus exponential-sum uniqueness theorem
    have hreindex : ∀ t : ℝ,
        ∑ i : Fin K.card, c (K.equivFin.symm i) * HTGeometry.cis (θ (K.equivFin.symm i)) t
          = expSumOn K c θ t := by
      intro t
      rw [expSumOn, ← Finset.sum_coe_sort K (fun j => c j * HTGeometry.cis (θ j) t)]
      exact Equiv.sum_comp K.equivFin.symm
        (fun y : K => c (y : ι) * HTGeometry.cis (θ (y : ι)) t)
    have hinjlam : Function.Injective (fun i : Fin K.card => θ (K.equivFin.symm i)) := by
      intro i₁ i₂ hii
      apply K.equivFin.symm.injective
      apply Subtype.ext
      exact hθinj _ (K.equivFin.symm i₁).2 _ (K.equivFin.symm i₂).2 hii
    have hzero' : Tendsto
        (fun t : ℝ => ∑ i : Fin K.card,
          c (K.equivFin.symm i) * HTGeometry.cis (θ (K.equivFin.symm i)) t) atTop (𝓝 0) := by
      simpa only [hreindex] using hzero
    have hall := HTGeometry.eq_zero_of_expSum_tendsto_zero K.card
      (fun i => θ (K.equivFin.symm i)) (fun i => c (K.equivFin.symm i)) hinjlam hzero'
    have := hall (K.equivFin ⟨j, hj⟩)
    simpa using this
  have hLsubset : L ⊂ J := by
    refine ⟨hLsub, fun hcon => ?_⟩
    have := hcon hj₀J
    exact (Finset.mem_filter.mp this).2 rfl
  have hLzero : ∀ j ∈ L, c j = 0 := by
    refine ih L hLsubset (fun i hi j hj hxij => hinj i (hLsub hi) j (hLsub hj) hxij) ?_
    refine ⟨P, fun p hp hPp => ?_⟩
    have hsplit := Finset.sum_filter_add_sum_filter_not J (fun j => (x j).re = a)
      (fun j => c j * (p : ℂ) ^ (-(x j)))
    have hKz : ∑ j ∈ K, c j * (p : ℂ) ^ (-(x j)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [hKzero j hj, zero_mul]
    rw [hK, hL] at *
    rw [hKz, zero_add, hP p hp hPp] at hsplit
    exact hsplit
  intro j hj
  by_cases hjK : (x j).re = a
  · exact hKzero j (Finset.mem_filter.mpr ⟨hj, hjK⟩)
  · exact hLzero j (Finset.mem_filter.mpr ⟨hj, hjK⟩)

end RHTower
