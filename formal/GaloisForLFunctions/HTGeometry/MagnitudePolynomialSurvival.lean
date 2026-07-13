import GaloisForLFunctions.HTGeometry.MagnitudeMonomialSurvival
import GaloisForLFunctions.HTGeometry.DifferentialMonomialGapValue

/-!
# Full-support magnitude survival of a degree-homogeneous differential polynomial

The single-monomial survival theorem is upgraded to a **sum** of degree-`D` differential monomials.
When the leading symbol at the minimal total order `O₀` is a nonzero polynomial, the differential
polynomial `∑ μ c μ • ∏ₜ f^{(μₜ)}` does not annihilate a full-support superlacunary `f`:  at the
balanced position `D·M − O₀`, the order-`O₀` monomials contribute the leading symbol value
`(coeff M f)^D · L.eval M` while every other atom — same order off-balance, or higher order — is
exponentially smaller by the quantitative valuation gap.  A reverse-triangle estimate then keeps the
coefficient nonzero.

This is the "combine monomials" layer over `coeff_diffMonomial_balanced_ne_zero`; three prep lemmas
(`exists_index_gt_of_sum_gt`, `poly_eval_eventually_lower_bound`, `atom_norm_bad_le`) isolate the
combinatorial and analytic inputs.
-/

open PowerSeries Finset Filter
open scoped Nat

namespace GaloisForLFunctions

/-- A tuple whose entries sum to more than `D·M` has an entry exceeding `M`. -/
theorem exists_index_gt_of_sum_gt {D : ℕ} (t : Fin D → ℕ) (M : ℕ)
    (hsum : D * M < ∑ i, t i) : ∃ i, M < t i := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have : (∑ i, t i) ≤ ∑ _i : Fin D, M := Finset.sum_le_sum (fun i _ => h i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

/-- A nonzero complex polynomial is eventually bounded below in modulus along the naturals. -/
theorem poly_eval_eventually_lower_bound (L : Polynomial ℂ) (hL : L ≠ 0) :
    ∃ cc : ℝ, 0 < cc ∧ ∃ N : ℕ, ∀ M : ℕ, N ≤ M → cc ≤ ‖L.eval (M : ℂ)‖ := by
  rcases eq_or_ne L.natDegree 0 with h0 | hpos
  · obtain ⟨a, ha, rfl⟩ := Polynomial.natDegree_eq_zero.mp h0
    refine ⟨‖a‖, ?_, 0, fun M _ => ?_⟩
    · simp only [ne_eq, Polynomial.C_eq_zero] at hL; positivity
    · simp
  · have hdeg : 0 < L.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hpos)
    have hcast : Tendsto (fun M : ℕ => ‖(M : ℂ)‖) atTop atTop := by
      simp only [Complex.norm_natCast]; exact tendsto_natCast_atTop_atTop
    have htend := Polynomial.tendsto_norm_atTop L hdeg hcast
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually_ge_atTop 1)
    exact ⟨1, one_pos, N, hN⟩

/-- Norm of a full-support differential-monomial atom at a *bad* (super-mean) source tuple: the
falling-factorial weight is at most `W^(∑μ)` and the modulus product is `exp(-∑ b)`, which the
quantitative gap pins below `exp(-((D+1)·b M + (D-1)·m₀))`. -/
theorem atom_norm_bad_le {f : ℂ⟦X⟧} {b : ℕ → ℝ} (hb : ∀ n, ‖(coeff n) f‖ = Real.exp (- b n))
    {D : ℕ} {M : ℕ} {m₀ : ℝ} (hgapgt : ∀ (t : Fin D → ℕ), (∃ i, M < t i) →
      ((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀ ≤ ∑ i, b (t i))
    (μ l : Fin D → ℕ) (W : ℕ) (hbnd : ∀ t, l t + μ t ≤ W) (hbad : ∃ i, M < l i + μ i) :
    ‖∏ t, ((coeff (l t + μ t)) f * (((l t + μ t).descFactorial (μ t) : ℂ)))‖
      ≤ ((W ^ (∑ t, μ t) : ℕ) : ℝ) * Real.exp (- (((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀)) := by
  rw [norm_prod]
  have hval : ∀ t, ‖(coeff (l t + μ t)) f * (((l t + μ t).descFactorial (μ t) : ℂ))‖
      = ((l t + μ t).descFactorial (μ t) : ℝ) * Real.exp (- b (l t + μ t)) := by
    intro t; rw [norm_mul, hb, Complex.norm_natCast, mul_comm]
  rw [Finset.prod_congr rfl (fun t _ => hval t), Finset.prod_mul_distrib, ← Real.exp_sum]
  have hw : (∏ t, ((l t + μ t).descFactorial (μ t) : ℝ)) ≤ ((W ^ (∑ t, μ t) : ℕ) : ℝ) := by
    rw [← Nat.cast_prod]; apply Nat.cast_le.mpr
    calc (∏ t, (l t + μ t).descFactorial (μ t))
        ≤ ∏ t, (l t + μ t) ^ (μ t) := Finset.prod_le_prod' (fun t _ => Nat.descFactorial_le_pow _ _)
      _ ≤ ∏ t, W ^ (μ t) := Finset.prod_le_prod' (fun t _ => Nat.pow_le_pow_left (hbnd t) _)
      _ = W ^ (∑ t, μ t) := by rw [Finset.prod_pow_eq_pow_sum]
  have hexp : Real.exp (∑ t, - b (l t + μ t))
      ≤ Real.exp (- (((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀)) := by
    apply Real.exp_le_exp.mpr
    have := hgapgt (fun t => l t + μ t) hbad
    rw [Finset.sum_neg_distrib]; linarith [this]
  calc (∏ t, ((l t + μ t).descFactorial (μ t) : ℝ)) * Real.exp (∑ t, -b (l t + μ t))
      ≤ ((W ^ (∑ t, μ t) : ℕ) : ℝ) * Real.exp (∑ t, -b (l t + μ t)) :=
        mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
    _ ≤ ((W ^ (∑ t, μ t) : ℕ) : ℝ) * Real.exp (- (((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

/-- Atom bound with an **abstract gap value** `G` in place of the fixed `(D+1)·b M + (D-1)·m₀`.
Decoupling the exponent from the arity is what lets the mixed-degree combine apply one uniform gap
(the top degree `+1`) to differential monomials of every arity. -/
theorem atom_norm_bad_le_gen {f : ℂ⟦X⟧} {b : ℕ → ℝ} (hb : ∀ n, ‖(coeff n) f‖ = Real.exp (- b n))
    {D : ℕ} {G : ℝ} (μ l : Fin D → ℕ) (W : ℕ) (hbnd : ∀ t, l t + μ t ≤ W)
    (hgap : G ≤ ∑ i, b (l i + μ i)) :
    ‖∏ t, ((coeff (l t + μ t)) f * (((l t + μ t).descFactorial (μ t) : ℂ)))‖
      ≤ ((W ^ (∑ t, μ t) : ℕ) : ℝ) * Real.exp (- G) := by
  rw [norm_prod]
  have hval : ∀ t, ‖(coeff (l t + μ t)) f * (((l t + μ t).descFactorial (μ t) : ℂ))‖
      = ((l t + μ t).descFactorial (μ t) : ℝ) * Real.exp (- b (l t + μ t)) := by
    intro t; rw [norm_mul, hb, Complex.norm_natCast, mul_comm]
  rw [Finset.prod_congr rfl (fun t _ => hval t), Finset.prod_mul_distrib, ← Real.exp_sum]
  have hw : (∏ t, ((l t + μ t).descFactorial (μ t) : ℝ)) ≤ ((W ^ (∑ t, μ t) : ℕ) : ℝ) := by
    rw [← Nat.cast_prod]; apply Nat.cast_le.mpr
    calc (∏ t, (l t + μ t).descFactorial (μ t))
        ≤ ∏ t, (l t + μ t) ^ (μ t) := Finset.prod_le_prod' (fun t _ => Nat.descFactorial_le_pow _ _)
      _ ≤ ∏ t, W ^ (μ t) := Finset.prod_le_prod' (fun t _ => Nat.pow_le_pow_left (hbnd t) _)
      _ = W ^ (∑ t, μ t) := by rw [Finset.prod_pow_eq_pow_sum]
  have hexp : Real.exp (∑ t, - b (l t + μ t)) ≤ Real.exp (- G) := by
    apply Real.exp_le_exp.mpr; rw [Finset.sum_neg_distrib]; linarith [hgap]
  calc (∏ t, ((l t + μ t).descFactorial (μ t) : ℝ)) * Real.exp (∑ t, -b (l t + μ t))
      ≤ ((W ^ (∑ t, μ t) : ℕ) : ℝ) * Real.exp (∑ t, -b (l t + μ t)) :=
        mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
    _ ≤ ((W ^ (∑ t, μ t) : ℕ) : ℝ) * Real.exp (- G) := mul_le_mul_of_nonneg_left hexp (by positivity)

/-- Norm of a sum of *bad* atoms over any sub-antidiagonal: at most the antidiagonal cardinality
`(N+1)^D` times the uniform per-atom bound `W^E · exp(-((D+1)·b M + (D-1)·m₀))`. -/
theorem badset_atom_sum_le {f : ℂ⟦X⟧} {b : ℕ → ℝ} (hb : ∀ n, ‖(coeff n) f‖ = Real.exp (- b n))
    {D : ℕ} {M : ℕ} {m₀ : ℝ} (hgapgt : ∀ (t : Fin D → ℕ), (∃ i, M < t i) →
      ((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀ ≤ ∑ i, b (t i))
    (μ : Fin D → ℕ) (N W E : ℕ) (hW1 : 1 ≤ W) (hmule : ∑ t, μ t ≤ E)
    (s' : Finset (Fin D →₀ ℕ)) (hsub : s' ⊆ (Finset.univ : Finset (Fin D)).finsuppAntidiag N)
    (hbnd : ∀ l ∈ s', ∀ t, l t + μ t ≤ W) (hbad : ∀ l ∈ s', ∃ i, M < l i + μ i) :
    ‖∑ l ∈ s', ∏ t, ((coeff (l t + μ t)) f * (((l t + μ t).descFactorial (μ t) : ℂ)))‖
      ≤ (((N + 1) ^ D : ℕ) : ℝ) * (((W ^ E : ℕ) : ℝ)
          * Real.exp (- (((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀))) := by
  classical
  calc ‖∑ l ∈ s', ∏ t, ((coeff (l t + μ t)) f * (((l t + μ t).descFactorial (μ t) : ℂ)))‖
      ≤ ∑ l ∈ s', ‖∏ t, ((coeff (l t + μ t)) f * (((l t + μ t).descFactorial (μ t) : ℂ)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _l ∈ s', (((W ^ E : ℕ) : ℝ) * Real.exp (- (((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀))) := by
        refine Finset.sum_le_sum fun l hl => ?_
        calc ‖∏ t, ((coeff (l t + μ t)) f * (((l t + μ t).descFactorial (μ t) : ℂ)))‖
            ≤ ((W ^ (∑ t, μ t) : ℕ) : ℝ) * Real.exp (- (((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀)) :=
              atom_norm_bad_le hb hgapgt μ l W (hbnd l hl) (hbad l hl)
          _ ≤ ((W ^ E : ℕ) : ℝ) * Real.exp (- (((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀)) :=
              mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.pow_le_pow_right hW1 hmule))
                (Real.exp_pos _).le
    _ = (s'.card : ℝ) * (((W ^ E : ℕ) : ℝ) * Real.exp (- (((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((N + 1) ^ D : ℕ) : ℝ) * (((W ^ E : ℕ) : ℝ)
          * Real.exp (- (((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀))) :=
        mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (le_trans (Finset.card_le_card hsub) antidiag_card_le)) (by positivity)

/-- Reverse-triangle domination arithmetic: the polynomial atom-count prefactor times `exp(-thr)` is
beaten by `cL · exp(-D·b M)` once the magnitude `b M` dominates the logarithm of the prefactor. -/
theorem poly_domination_bound (D Omax : ℕ) (Q Nr DMr bM m₀ cL CS : ℝ)
    (hcL : 0 < cL) (hCS : 0 < CS) (hNrpos : 0 < Nr) (hDMrpos : 0 < DMr)
    (hlogN : Real.log Nr ≤ Real.log ((D : ℝ) + 1) + Real.log Q)
    (hlogD : Real.log DMr ≤ Real.log ((D : ℝ) + (Omax : ℝ)) + Real.log Q)
    (hgrow : ((D : ℝ) + Omax) * Real.log Q
        + (Real.log CS + D * Real.log ((D : ℝ) + 1) + Omax * Real.log ((D : ℝ) + Omax)
           - ((D : ℝ) - 1) * m₀ - Real.log cL + 1) ≤ bM) :
    CS * (Nr ^ D * DMr ^ Omax) * Real.exp (-(((D : ℝ) + 1) * bM + ((D : ℝ) - 1) * m₀))
      < cL * Real.exp (-(D : ℝ) * bM) := by
  have hlogP : Real.log (CS * (Nr ^ D * DMr ^ Omax))
      = Real.log CS + D * Real.log Nr + Omax * Real.log DMr := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]; ring
  have hkey : Real.log CS + D * Real.log Nr + Omax * Real.log DMr - ((D : ℝ) - 1) * m₀
      < bM + Real.log cL := by
    have h1 : (D : ℝ) * Real.log Nr ≤ D * (Real.log ((D : ℝ) + 1) + Real.log Q) :=
      mul_le_mul_of_nonneg_left hlogN (by positivity)
    have h2 : (Omax : ℝ) * Real.log DMr ≤ Omax * (Real.log ((D : ℝ) + Omax) + Real.log Q) :=
      mul_le_mul_of_nonneg_left hlogD (by positivity)
    nlinarith [hgrow, h1, h2]
  have hexp : CS * (Nr ^ D * DMr ^ Omax) * Real.exp (-((D : ℝ) - 1) * m₀) < cL * Real.exp bM := by
    have hLpos : (0 : ℝ) < CS * (Nr ^ D * DMr ^ Omax) * Real.exp (-((D : ℝ) - 1) * m₀) := by positivity
    have hRpos : (0 : ℝ) < cL * Real.exp bM := by positivity
    rw [← Real.exp_log hLpos, ← Real.exp_log hRpos]
    apply Real.exp_lt_exp.mpr
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
        Real.log_mul (ne_of_gt hcL) (Real.exp_ne_zero _), Real.log_exp, hlogP]
    linarith [hkey]
  calc CS * (Nr ^ D * DMr ^ Omax) * Real.exp (-(((D : ℝ) + 1) * bM + ((D : ℝ) - 1) * m₀))
      = (CS * (Nr ^ D * DMr ^ Omax) * Real.exp (-((D : ℝ) - 1) * m₀)) * Real.exp (-((D : ℝ) + 1) * bM) := by
        rw [show (-(((D : ℝ) + 1) * bM + ((D : ℝ) - 1) * m₀))
          = (-((D : ℝ) - 1) * m₀) + (-((D : ℝ) + 1) * bM) by ring, Real.exp_add]; ring
    _ < (cL * Real.exp bM) * Real.exp (-((D : ℝ) + 1) * bM) := mul_lt_mul_of_pos_right hexp (Real.exp_pos _)
    _ = cL * Real.exp (-(D : ℝ) * bM) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- **Degree-homogeneous full-support magnitude survival.**  A sum of degree-`D` differential
monomials whose leading symbol at the minimal total order `O₀` is a nonzero polynomial does not
annihilate a full-support superlacunary series `f`:  at the balanced position `D·M − O₀` the
order-`O₀` monomials contribute `(coeff M f)^D · L.eval M`, dominating every other atom via the
quantitative valuation gap, so a reverse-triangle estimate keeps the coefficient nonzero. -/
theorem coeff_degHomDiffPoly_magnitude_ne_zero {f : ℂ⟦X⟧} {b : ℕ → ℝ}
    (hb : ∀ n, ‖(coeff n) f‖ = Real.exp (- b n))
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop)
    {D : ℕ} (hD : 0 < D) (O₀ : ℕ) (S : Finset (Fin D → ℕ)) (c : (Fin D → ℕ) → ℂ)
    (hOmin : ∀ μ ∈ S, O₀ ≤ ∑ t, μ t)
    (hLead : (∑ μ ∈ S.filter (fun μ => ∑ t, μ t = O₀), c μ • ∏ t, descPochhammer ℂ (μ t)) ≠ 0) :
    (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) ≠ 0 := by
  classical
  set S₀ := S.filter (fun μ => ∑ t, μ t = O₀) with hS₀def
  set L := ∑ μ ∈ S₀, c μ • ∏ t, descPochhammer ℂ (μ t) with hLdef
  obtain ⟨cL, hcLpos, NL, hNL⟩ := poly_eval_eventually_lower_bound L hLead
  obtain ⟨Ng, m₀, hm₀, hgapgt0⟩ := tuple_valuation_gap_lower_gt hpos hratio hD
  set Omax := S.sup (fun μ => ∑ t, μ t) with hOmaxdef
  set maxJS := S.sup (fun μ => Finset.univ.sup μ) with hmaxJSdef
  set CS := ∑ μ ∈ S, ‖c μ‖ with hCSdef
  -- CS > 0 from L ≠ 0
  have hex : ∃ μ ∈ S₀, c μ ≠ 0 := by
    by_contra h; simp only [not_exists, not_and, not_not] at h
    exact hLead (by rw [hLdef]; exact Finset.sum_eq_zero fun μ hμ => by rw [h μ hμ, zero_smul])
  obtain ⟨μ0, hμ0S₀, hcμ0⟩ := hex
  have hμ0S : μ0 ∈ S := Finset.mem_of_mem_filter _ hμ0S₀
  have hCSpos : 0 < CS :=
    Finset.sum_pos' (fun _ _ => norm_nonneg _) ⟨μ0, hμ0S, norm_pos_iff.mpr hcμ0⟩
  -- growth
  set Kg : ℝ := Real.log CS + D * Real.log ((D : ℝ) + 1) + Omax * Real.log ((D : ℝ) + Omax)
      - ((D : ℝ) - 1) * m₀ - Real.log cL + 1 with hKgdef
  obtain ⟨Nd, hNd⟩ := exists_dominates_log hpos hratio ((D : ℝ) + Omax) Kg
  set M := max (max (max NL Ng) (max Nd 1)) maxJS with hMdef
  have hNLM : NL ≤ M := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) le_rfl
  have hNgM : Ng ≤ M := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) le_rfl
  have hNdM : Nd ≤ M := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) le_rfl
  have hM1 : 1 ≤ M := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) le_rfl
  have hmaxJSM : maxJS ≤ M := le_max_right _ _
  have hgapgt := hgapgt0 M hNgM
  -- μ t ≤ M for μ ∈ S
  have hMμ : ∀ μ ∈ S, ∀ t, μ t ≤ M := fun μ hμ t =>
    le_trans (le_trans (Finset.le_sup (Finset.mem_univ t))
      (Finset.le_sup (f := fun μ => Finset.univ.sup μ) hμ)) hmaxJSM
  -- ∑ μ ≤ Omax and Omax ≤ D * M
  have hsumμ_le : ∀ μ ∈ S, ∑ t, μ t ≤ Omax := fun μ hμ => Finset.le_sup hμ
  have hOmaxDM : Omax ≤ D * M := by
    rcases S.eq_empty_or_nonempty with hSe | ⟨ν, hν⟩
    · simp [hOmaxdef, hSe]
    · rw [hOmaxdef, Finset.sup_le_iff]
      intro μ hμ
      calc ∑ t, μ t ≤ ∑ _t : Fin D, M := Finset.sum_le_sum (fun t _ => hMμ μ hμ t)
        _ = D * M := by simp [Finset.card_univ]
  have hO₀le : O₀ ≤ D * M := le_trans (le_trans (hOmin μ0 hμ0S) (hsumμ_le μ0 hμ0S)) hOmaxDM
  set N := D * M - O₀ with hNdef
  have hNsj : N + O₀ = D * M := by omega
  have hNleDM : N ≤ D * M := by omega
  -- balanced index for μ
  set balF : (Fin D → ℕ) → (Fin D →₀ ℕ) := fun μ =>
    Finsupp.onFinset Finset.univ (fun t => M - μ t) (fun a _ => Finset.mem_univ a) with hbalF
  have hbalapp : ∀ μ t, (balF μ) t = M - μ t := fun μ t => Finsupp.onFinset_apply
  have hbalshift : ∀ μ ∈ S, ∀ t, (balF μ) t + μ t = M := fun μ hμ t => by
    have := hMμ μ hμ t; rw [hbalapp]; omega
  -- atom abbreviation
  let atom : (Fin D → ℕ) → (Fin D →₀ ℕ) → ℂ :=
    fun μ l => ∏ t, ((coeff (l t + μ t)) f * (((l t + μ t).descFactorial (μ t) : ℂ)))
  -- Stage 1
  have hstage1 : (coeff N) (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f)
      = ∑ μ ∈ S, c μ * ∑ l ∈ (Finset.univ : Finset (Fin D)).finsuppAntidiag N, atom μ l := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun μ _ => by
      rw [map_smul, smul_eq_mul, coeff_prod_iterate_deriv f μ N]
  -- A' and its value
  set A' : ℂ := ∑ μ ∈ S₀, c μ * atom μ (balF μ) with hA'def
  have hAval : A' = (coeff M f) ^ D * L.eval (M : ℂ) := by
    rw [hA'def, hLdef, Polynomial.eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hμS : μ ∈ S := Finset.mem_of_mem_filter _ hμ
    show c μ * (∏ t, ((coeff ((balF μ) t + μ t)) f * ((((balF μ) t + μ t).descFactorial (μ t) : ℂ)))) = _
    rw [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_prod,
      Finset.prod_congr rfl (fun t _ => by rw [hbalshift μ hμS t]),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_congr rfl (fun t _ => descPochhammer_eval_eq_descFactorial ℂ M (μ t))]
    ring
  -- membership of balanced index
  have hbalmem : ∀ μ ∈ S₀, balF μ ∈ (Finset.univ : Finset (Fin D)).finsuppAntidiag N := by
    intro μ hμ
    have hμS : μ ∈ S := Finset.mem_of_mem_filter _ hμ
    have hμO : ∑ t, μ t = O₀ := (Finset.mem_filter.mp hμ).2
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finsupp.support_onFinset_subset⟩
    rw [Finset.sum_congr rfl (fun t _ => hbalapp μ t)]
    have : (∑ t, (M - μ t)) + O₀ = D * M := by
      rw [← hμO, ← Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun t _ => Nat.sub_add_cancel (hMμ μ hμS t))]
      simp [Finset.card_univ]
    omega
  -- source bound: l t + μ t ≤ D*M + Omax
  have hktle : ∀ μ ∈ S, ∀ l ∈ (Finset.univ : Finset (Fin D)).finsuppAntidiag N, ∀ t,
      l t + μ t ≤ D * M + Omax := by
    intro μ hμ l hl t
    rw [Finset.mem_finsuppAntidiag] at hl
    have hlt : l t ≤ N := hl.1 ▸ Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t)
    have hjt : μ t ≤ Omax := le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le _)
      (Finset.mem_univ t)) (hsumμ_le μ hμ)
    omega
  -- W ≥ 1
  have hW1 : 1 ≤ D * M + Omax := by have : 0 < D * M := Nat.mul_pos hD (by omega); omega
  -- per-μ bound abbreviation
  set Bnd : ℝ := (((N + 1) ^ D : ℕ) : ℝ) * ((((D * M + Omax) ^ Omax : ℕ) : ℝ)
      * Real.exp (- (((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀))) with hBnddef
  have hBndnn : 0 ≤ Bnd := by rw [hBnddef]; positivity
  -- S₀ case
  have hS₀case : ∀ μ ∈ S₀, ‖(∑ l ∈ (Finset.univ : Finset (Fin D)).finsuppAntidiag N, atom μ l)
      - atom μ (balF μ)‖ ≤ Bnd := by
    intro μ hμ
    have hμS : μ ∈ S := Finset.mem_of_mem_filter _ hμ
    have hμO : ∑ t, μ t = O₀ := (Finset.mem_filter.mp hμ).2
    rw [← Finset.add_sum_erase _ (atom μ) (hbalmem μ hμ), add_sub_cancel_left]
    exact badset_atom_sum_le hb hgapgt μ N (D * M + Omax) Omax hW1 (hsumμ_le μ hμS)
      ((Finset.univ.finsuppAntidiag N).erase (balF μ)) (Finset.erase_subset _ _)
      (fun l hl => hktle μ hμS l (Finset.mem_of_mem_erase hl))
      (fun l hl => by
        obtain ⟨hlne, hlmem⟩ := Finset.mem_erase.mp hl
        rw [Finset.mem_finsuppAntidiag] at hlmem
        refine exists_index_gt_of_sum_eq (fun t => l t + μ t) M ?_ ?_
        · rw [Finset.sum_add_distrib, hlmem.1, hμO]; omega
        · by_contra hall; simp only [not_exists, not_ne_iff] at hall
          exact hlne (by ext t; have := hall t; have := hMμ μ hμS t; rw [hbalapp]; omega))
  -- S ∖ S₀ case
  have hScase : ∀ μ ∈ S.filter (fun μ => ¬ ∑ t, μ t = O₀),
      ‖∑ l ∈ (Finset.univ : Finset (Fin D)).finsuppAntidiag N, atom μ l‖ ≤ Bnd := by
    intro μ hμ
    obtain ⟨hμS, hμne⟩ := Finset.mem_filter.mp hμ
    have hμgt : O₀ < ∑ t, μ t := lt_of_le_of_ne (hOmin μ hμS) (Ne.symm hμne)
    exact badset_atom_sum_le hb hgapgt μ N (D * M + Omax) Omax hW1 (hsumμ_le μ hμS)
      (Finset.univ.finsuppAntidiag N) (Finset.Subset.refl _) (fun l hl => hktle μ hμS l hl)
      (fun l hl => by
        rw [Finset.mem_finsuppAntidiag] at hl
        refine exists_index_gt_of_sum_gt (fun t => l t + μ t) M ?_
        rw [Finset.sum_add_distrib, hl.1]; omega)
    -- assemble ‖coeff N (diffpoly) - A'‖ ≤ CS * Bnd
  have hsplit : (coeff N) (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) - A'
      = (∑ μ ∈ S₀, c μ * ((∑ l ∈ (Finset.univ : Finset (Fin D)).finsuppAntidiag N, atom μ l)
            - atom μ (balF μ)))
        + ∑ μ ∈ S.filter (fun μ => ¬ ∑ t, μ t = O₀),
            c μ * ∑ l ∈ (Finset.univ : Finset (Fin D)).finsuppAntidiag N, atom μ l := by
    rw [hstage1, hA'def, ← Finset.sum_filter_add_sum_filter_not S (fun μ => ∑ t, μ t = O₀)
      (fun μ => c μ * ∑ l ∈ (Finset.univ : Finset (Fin D)).finsuppAntidiag N, atom μ l), ← hS₀def]
    simp only [mul_sub, Finset.sum_sub_distrib]
    abel
  have hRbound : ‖(coeff N) (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) - A'‖ ≤ CS * Bnd := by
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hb1 : ‖∑ μ ∈ S₀, c μ * ((∑ l ∈ (Finset.univ : Finset (Fin D)).finsuppAntidiag N, atom μ l)
        - atom μ (balF μ))‖ ≤ ∑ μ ∈ S₀, ‖c μ‖ * Bnd := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun μ hμ => ?_)
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hS₀case μ hμ) (norm_nonneg _)
    have hb2 : ‖∑ μ ∈ S.filter (fun μ => ¬ ∑ t, μ t = O₀),
        c μ * ∑ l ∈ (Finset.univ : Finset (Fin D)).finsuppAntidiag N, atom μ l‖
        ≤ ∑ μ ∈ S.filter (fun μ => ¬ ∑ t, μ t = O₀), ‖c μ‖ * Bnd := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun μ hμ => ?_)
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hScase μ hμ) (norm_nonneg _)
    calc ‖_‖ + ‖_‖ ≤ (∑ μ ∈ S₀, ‖c μ‖ * Bnd) + ∑ μ ∈ S.filter (fun μ => ¬ ∑ t, μ t = O₀), ‖c μ‖ * Bnd :=
          add_le_add hb1 hb2
      _ = (∑ μ ∈ S, ‖c μ‖) * Bnd := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul]; congr 1
          exact Finset.sum_filter_add_sum_filter_not S (fun μ => ∑ t, μ t = O₀) (fun μ => ‖c μ‖)
      _ = CS * Bnd := by rw [hCSdef]
  -- ‖A'‖ lower bound
  have hApos : cL * Real.exp (-(D:ℝ) * b M) ≤ ‖A'‖ := by
    rw [hAval, norm_mul, norm_pow, hb M]
    rw [show (Real.exp (-b M)) ^ D = Real.exp (-(D:ℝ) * b M) by
      rw [← Real.exp_nat_mul]; congr 1; ring]
    rw [mul_comm cL]
    exact mul_le_mul_of_nonneg_left (hNL M hNLM) (Real.exp_pos _).le
  -- domination
  have hQ : (0:ℝ) < (M:ℝ) + 2 := by positivity
  have hDMrpos : (0:ℝ) < (D:ℝ) * M + Omax := by
    have : (1:ℝ) ≤ (D:ℝ)*M + Omax := by exact_mod_cast hW1; 
    linarith
  have hlogNr : Real.log ((N:ℝ)+1) ≤ Real.log ((D:ℝ)+1) + Real.log ((M:ℝ)+2) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    have : (N:ℝ) ≤ (D:ℝ)*M := by exact_mod_cast hNleDM
    nlinarith [Nat.cast_nonneg D (α:=ℝ), Nat.cast_nonneg M (α:=ℝ), this]
  have hlogDMr : Real.log ((D:ℝ)*M+Omax) ≤ Real.log ((D:ℝ)+Omax) + Real.log ((M:ℝ)+2) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log hDMrpos
    nlinarith [Nat.cast_nonneg D (α:=ℝ), Nat.cast_nonneg M (α:=ℝ), Nat.cast_nonneg Omax (α:=ℝ)]
  have hgrow := hNd M hNdM
  have hdom : CS * Bnd < cL * Real.exp (-(D:ℝ) * b M) := by
    have hpd := poly_domination_bound D Omax ((M:ℝ)+2) ((N:ℝ)+1) ((D:ℝ)*M+Omax) (b M) m₀ cL CS
      hcLpos hCSpos (by positivity) hDMrpos hlogNr hlogDMr (by rw [hKgdef] at hgrow; exact hgrow)
    rw [hBnddef]
    calc CS * ((((N + 1) ^ D : ℕ) : ℝ) * ((((D * M + Omax) ^ Omax : ℕ) : ℝ)
          * Real.exp (- (((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀))))
        = CS * (((N:ℝ)+1) ^ D * ((D:ℝ)*M+Omax) ^ Omax)
            * Real.exp (-(((D : ℝ) + 1) * b M + ((D : ℝ) - 1) * m₀)) := by push_cast; ring
      _ < cL * Real.exp (-(D:ℝ) * b M) := hpd
  -- conclude
  refine fun hzero => ?_
  have hc0 : (coeff N) (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) = 0 := by rw [hzero, map_zero]
  have hcontra : ‖A'‖ < ‖A'‖ := by
    calc ‖A'‖ = ‖(0 : ℂ) - A'‖ := by rw [zero_sub, norm_neg]
      _ = ‖(coeff N) (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) - A'‖ := by rw [hc0]
      _ ≤ CS * Bnd := hRbound
      _ < cL * Real.exp (-(D:ℝ) * b M) := hdom
      _ ≤ ‖A'‖ := hApos
  exact absurd hcontra (lt_irrefl _)

end GaloisForLFunctions
