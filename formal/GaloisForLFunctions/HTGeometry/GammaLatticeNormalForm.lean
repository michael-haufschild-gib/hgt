import GaloisForLFunctions.HTGeometry.GammaFiberDatum

/-!
# The normal-form datum over a lattice of shifts

`NoIntegerRelation` is false for a rank-two lattice of shifts, and it was used only to make the
dominance classes singletons.  Grouping the sum by the pair `(Γ-degree, first moment)` instead makes
the classes exactly the fibres, whose data come from `GammaFiberDatum`; distinct fibres never
collide as soon as no nonzero integer combination of the shifts is a **nonzero** integer, which is
strictly weaker than `NoIntegerRelation` and is what the prime-log lattice supplies.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

variable {r : ℕ}

/-- No nonzero integer combination of the shifts is a nonzero integer. -/
def NoNonzeroIntegerValue {rr : ℕ} (lamf : Fin rr → ℝ) : Prop :=
  ∀ (n : Fin rr → ℤ) (m : ℤ), (∑ k, (n k : ℝ) * lamf k) = (m : ℝ) →
    (∑ k, (n k : ℝ) * lamf k) = 0

theorem TubeLimit.const_mul {M : ℝ} {f : ℝ → ℝ → ℂ} {c : ℂ} (h : TubeLimit M f c) (k : ℂ) :
    TubeLimit M (fun σ t => k * f σ t) (k * c) := by
  intro ε hε
  rcases eq_or_ne k 0 with hk | hk
  · refine ⟨2, fun σ t _ _ _ => ?_⟩
    rw [hk]
    simp only [zero_mul, sub_self, norm_zero]
    linarith
  · obtain ⟨T, hT⟩ := h (ε / ‖k‖) (by positivity)
    refine ⟨T, fun σ t hσ hσM ht => ?_⟩
    have hb := hT σ t hσ hσM ht
    have hkpos : (0 : ℝ) < ‖k‖ := norm_pos_iff.mpr hk
    rw [← mul_sub, norm_mul]
    calc ‖k‖ * ‖f σ t - c‖ ≤ ‖k‖ * (ε / ‖k‖) :=
          mul_le_mul_of_nonneg_left hb (le_of_lt hkpos)
      _ = ε := by field_simp

theorem HasShiftTubeDatum.const_mul {M lam : ℝ} {φ : ℝ → ℝ → ℂ} {d : ℤ} {ω : ℝ} {b : ℤ} {c k : ℂ}
    (h : HasShiftTubeDatum M lam φ d ω b c) (hk : k ≠ 0) :
    HasShiftTubeDatum M lam (fun σ t => k * φ σ t) d ω b (k * c) := by
  refine ⟨mul_ne_zero hk h.1, ?_⟩
  have hm := h.2.const_mul k
  refine hm.congr (T₀ := 0) fun σ t _ _ _ => ?_
  rw [mul_div_assoc]

/-- **The normal-form datum over a lattice of shifts.** -/
theorem exists_hasShiftTubeDatum_jetGammaLatticeSum {M : ℝ} (hM : 0 < M) {K Mm : ℕ}
    (hMm : 0 < Mm) (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hlat : NoNonzeroIntegerValue lam)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    (idx : Fin K → Fin r × ℕ) (hinj : Function.Injective idx)
    (ee : Fin Mm → Fin r → ℕ) (hee : Function.Injective ee)
    (P : Fin Mm → MvPolynomial (Fin K) (Polynomial ℂ)) (hP : ∀ i, P i ≠ 0) :
    ∃ (d : ℤ) (ω : ℝ) (b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => ∑ α : Fin Mm, jetFieldPolyFun lam idx (P α) ((σ : ℂ) + (t : ℂ) * Complex.I)
          * ∏ k : Fin r, gammaLine (σ + lam k) t ^ ee α k) d ω b c := by
  classical
  set term : Fin Mm → ℝ → ℝ → ℂ :=
    fun α σ t => jetFieldPolyFun lam idx (P α) ((σ : ℂ) + (t : ℂ) * Complex.I)
      * ∏ k : Fin r, gammaLine (σ + lam k) t ^ ee α k with hterm
  set keyf : Fin Mm → ℤ × ℝ :=
    fun α => (∑ k, (ee α k : ℤ), ∑ k, (ee α k : ℝ) * lam k) with hkeyf
  set fib : Fin Mm → Finset (Fin Mm) :=
    fun α => Finset.univ.filter (fun β => keyf β = keyf α) with hfib
  have hmemself : ∀ α, α ∈ fib α := by
    intro α
    rw [hfib]
    simp
  have hfibmem : ∀ α β, β ∈ fib α → keyf β = keyf α := by
    intro α β hb
    rw [hfib] at hb
    exact (Finset.mem_filter.mp hb).2
  have hfibeq : ∀ α β, keyf α = keyf β → fib α = fib β := by
    intro α β h
    rw [hfib]
    simp only
    rw [h]
  have hne : ∀ α, (fib α).Nonempty := fun α => ⟨α, hmemself α⟩
  set rep : Fin Mm → Fin Mm := fun α => (fib α).min' (hne α) with hrep
  have hrepmem : ∀ α, rep α ∈ fib α := fun α => (fib α).min'_mem (hne α)
  have hkeyrep : ∀ α, keyf (rep α) = keyf α := fun α => hfibmem α _ (hrepmem α)
  have hdatum : ∀ α : Fin Mm, ∃ (a b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0 (fun σ t => ∑ β ∈ fib α, term β σ t)
        (∑ k : Fin r, (ee (rep α) k : ℤ))
        ((a : ℝ) + ∑ k : Fin r, (ee (rep α) k : ℝ) * lam k) b c := by
    intro α
    refine exists_hasShiftTubeDatum_gammaFiberSum hM lam hlam hincong idx hinj ee hee P
      (fib α) (rep α) (hrepmem α) (hP (rep α)) ?_ ?_
    · intro β hβ
      have h1 := hfibmem α β hβ
      have h2 := hkeyrep α
      rw [hkeyf] at h1 h2
      exact (Prod.ext_iff.mp h1).1.trans (Prod.ext_iff.mp h2).1.symm
    · intro β hβ
      have h1 := hfibmem α β hβ
      have h2 := hkeyrep α
      rw [hkeyf] at h1 h2
      exact (Prod.ext_iff.mp h1).2.trans (Prod.ext_iff.mp h2).2.symm
  choose aa bb cc hcc hdd using hdatum
  set nn : Fin Mm → ℕ := fun α => (fib α).card with hnn
  have hnnpos : ∀ α, 0 < nn α := fun α => Finset.card_pos.mpr (hne α)
  have hnnne : ∀ α, ((nn α : ℂ)) ≠ 0 := by
    intro α
    have h0 : nn α ≠ 0 := by have := hnnpos α; omega
    exact_mod_cast Nat.cast_ne_zero.mpr h0
  set F : Fin Mm → ℝ → ℝ → ℂ :=
    fun α σ t => (1 / (nn α : ℂ)) * ∑ β ∈ fib α, term β σ t with hF
  have hFdat : ∀ α, HasShiftTubeDatum M 0 (F α)
      (∑ k : Fin r, (ee (rep α) k : ℤ))
      ((aa α : ℝ) + ∑ k : Fin r, (ee (rep α) k : ℝ) * lam k) (bb α)
      ((1 / (nn α : ℂ)) * cc α) := fun α => (hdd α).const_mul (one_div_ne_zero (hnnne α))
  -- two indices in one fibre carry the same datum
  have hFeq : ∀ α β : Fin Mm, keyf α = keyf β → F α = F β := by
    intro α β h
    rw [hF]
    funext σ t
    simp only
    rw [hfibeq α β h, hnn]
    simp only
    rw [hfibeq α β h]
  have hdataeq : ∀ α β : Fin Mm, keyf α = keyf β →
      (∑ k : Fin r, (ee (rep α) k : ℤ)) = (∑ k : Fin r, (ee (rep β) k : ℤ))
      ∧ ((aa α : ℝ) + ∑ k : Fin r, (ee (rep α) k : ℝ) * lam k)
        = ((aa β : ℝ) + ∑ k : Fin r, (ee (rep β) k : ℝ) * lam k)
      ∧ bb α = bb β ∧ (1 / (nn α : ℂ)) * cc α = (1 / (nn β : ℂ)) * cc β := by
    intro α β h
    have hβdat := hFdat β
    rw [← hFeq α β h] at hβdat
    exact hasShiftTubeDatum_unique hM le_rfl (hFdat α) hβdat
  have hsum : ∀ σ t : ℝ, ∑ α : Fin Mm, F α σ t = ∑ α : Fin Mm, term α σ t := by
    intro σ t
    have hmaps : ∀ α ∈ (Finset.univ : Finset (Fin Mm)),
        keyf α ∈ Finset.image keyf Finset.univ :=
      fun α _ => Finset.mem_image_of_mem _ (Finset.mem_univ α)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun α => F α σ t),
      ← Finset.sum_fiberwise_of_maps_to hmaps (fun α => term α σ t)]
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨α₀, -, rfl⟩ := Finset.mem_image.mp hy
    have hfil : (Finset.univ.filter (fun α => keyf α = keyf α₀)) = fib α₀ := by
      rw [hfib]
    rw [hfil]
    have hconst : ∀ α ∈ fib α₀, F α σ t = (1 / (nn α₀ : ℂ)) * ∑ β ∈ fib α₀, term β σ t := by
      intro α hα
      have hfe : fib α = fib α₀ := hfibeq α α₀ (hfibmem α₀ α hα)
      rw [hF]
      simp only
      rw [hfe, hnn]
      simp only
      rw [hfe]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hcast : ((fib α₀).card : ℂ) = (nn α₀ : ℂ) := rfl
    rw [hcast]
    have hcard : ((nn α₀ : ℂ)) ≠ 0 := hnnne α₀
    field_simp
  have hclassmem : ∀ α β : Fin Mm,
      ((∑ k : Fin r, (ee (rep α) k : ℤ)) = (∑ k : Fin r, (ee (rep β) k : ℤ))
        ∧ ((aa α : ℝ) + ∑ k : Fin r, (ee (rep α) k : ℝ) * lam k)
          = ((aa β : ℝ) + ∑ k : Fin r, (ee (rep β) k : ℝ) * lam k)
        ∧ bb α = bb β) → keyf α = keyf β := by
    rintro α β ⟨h1, h2, -⟩
    have hsplit : ∑ k : Fin r, ((((ee (rep α) k : ℤ) - (ee (rep β) k : ℤ)) : ℤ) : ℝ) * lam k
        = (∑ k : Fin r, (ee (rep α) k : ℝ) * lam k)
          - (∑ k : Fin r, (ee (rep β) k : ℝ) * lam k) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    have hcomb : ∑ k : Fin r, ((((ee (rep α) k : ℤ) - (ee (rep β) k : ℤ)) : ℤ) : ℝ) * lam k
        = (((aa β - aa α : ℤ)) : ℝ) := by
      rw [hsplit]
      push_cast
      linarith
    have hzero := hlat (fun k => (ee (rep α) k : ℤ) - (ee (rep β) k : ℤ)) (aa β - aa α) hcomb
    rw [hsplit] at hzero
    have hmomeq : (∑ k : Fin r, (ee (rep α) k : ℝ) * lam k)
        = (∑ k : Fin r, (ee (rep β) k : ℝ) * lam k) := by linarith
    have hrepkey : keyf (rep α) = keyf (rep β) := by
      rw [hkeyf]
      simp only
      exact Prod.ext h1 hmomeq
    rw [← hkeyrep α, ← hkeyrep β, hrepkey]
  have hfilter : ∀ β : Fin Mm, (Finset.univ.filter (fun α : Fin Mm =>
      (∑ k : Fin r, (ee (rep α) k : ℤ)) = (∑ k : Fin r, (ee (rep β) k : ℤ))
        ∧ ((aa α : ℝ) + ∑ k : Fin r, (ee (rep α) k : ℝ) * lam k)
          = ((aa β : ℝ) + ∑ k : Fin r, (ee (rep β) k : ℝ) * lam k)
        ∧ bb α = bb β)) = fib β := by
    intro β
    ext α
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rw [hfib]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hclassmem α β h
    · intro hα
      obtain ⟨e1, e2, e3, -⟩ := hdataeq α β (hfibmem β α hα)
      exact ⟨e1, e2, e3⟩
  have hclasssum : ∀ β : Fin Mm, (∑ α ∈ Finset.univ.filter (fun α : Fin Mm =>
      (∑ k : Fin r, (ee (rep α) k : ℤ)) = (∑ k : Fin r, (ee (rep β) k : ℤ))
        ∧ ((aa α : ℝ) + ∑ k : Fin r, (ee (rep α) k : ℝ) * lam k)
          = ((aa β : ℝ) + ∑ k : Fin r, (ee (rep β) k : ℝ) * lam k)
        ∧ bb α = bb β), (1 / (nn α : ℂ)) * cc α) = cc β := by
    intro β
    rw [hfilter β]
    have hconst : ∀ α ∈ fib β, (1 / (nn α : ℂ)) * cc α = (1 / (nn β : ℂ)) * cc β :=
      fun α hα => (hdataeq α β (hfibmem β α hα)).2.2.2
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hcast : ((fib β).card : ℂ) = (nn β : ℂ) := rfl
    rw [hcast]
    have hcard : ((nn β : ℂ)) ≠ 0 := hnnne β
    field_simp
  obtain ⟨β, hβ⟩ := exists_hasShiftTubeDatum_sum_class hM le_rfl hMm F
    (fun α => ∑ k : Fin r, (ee (rep α) k : ℤ))
    (fun α => (aa α : ℝ) + ∑ k : Fin r, (ee (rep α) k : ℝ) * lam k)
    bb (fun α => (1 / (nn α : ℂ)) * cc α) hFdat
    (fun β _ => by rw [hclasssum β]; exact hcc β)
  rw [hclasssum β] at hβ
  exact ⟨_, _, _, _, hcc β, hβ.congr_tube (T₀ := 0) fun σ t _ _ _ => hsum σ t⟩

/-- **The boundary datum of an arbitrary element of the shifted Gamma field over a lattice.**  An
element is a quotient of two normal-form sums, and data divide. -/
theorem exists_hasShiftTubeDatum_jetGammaLatticeQuotient {M : ℝ} (hM : 0 < M) {K Mm Mm' : ℕ}
    (hMm : 0 < Mm) (hMm' : 0 < Mm') (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hlat : NoNonzeroIntegerValue lam)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    (idx : Fin K → Fin r × ℕ) (hinj : Function.Injective idx)
    (ee : Fin Mm → Fin r → ℕ) (hee : Function.Injective ee)
    (P : Fin Mm → MvPolynomial (Fin K) (Polynomial ℂ)) (hP : ∀ i, P i ≠ 0)
    (ee' : Fin Mm' → Fin r → ℕ) (hee' : Function.Injective ee')
    (P' : Fin Mm' → MvPolynomial (Fin K) (Polynomial ℂ)) (hP' : ∀ i, P' i ≠ 0) :
    ∃ (d : ℤ) (ω : ℝ) (b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t =>
          (∑ α : Fin Mm, jetFieldPolyFun lam idx (P α) ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ∏ k : Fin r, gammaLine (σ + lam k) t ^ ee α k)
          / ∑ α : Fin Mm', jetFieldPolyFun lam idx (P' α) ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ∏ k : Fin r, gammaLine (σ + lam k) t ^ ee' α k) d ω b c := by
  obtain ⟨d, ω, b, c, hc, hdat⟩ := exists_hasShiftTubeDatum_jetGammaLatticeSum hM hMm lam hlam
    hlat hincong idx hinj ee hee P hP
  obtain ⟨d', ω', b', c', hc', hdat'⟩ := exists_hasShiftTubeDatum_jetGammaLatticeSum hM hMm' lam
    hlam hlat hincong idx hinj ee' hee' P' hP'
  exact ⟨_, _, _, _, div_ne_zero hc hc', hdat.div le_rfl hdat'⟩

end

end GaloisForLFunctions.HTGeometry
