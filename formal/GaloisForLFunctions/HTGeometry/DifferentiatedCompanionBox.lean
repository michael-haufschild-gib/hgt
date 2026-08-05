import GaloisForLFunctions.HTGeometry.PointwiseIntegerMonomial
import GaloisForLFunctions.HTGeometry.DifferentiatedCompanionObstruction
import GaloisForLFunctions.HTGeometry.MovingCanonicalFullRankUnconditional

/-!
# A closed full-rank datum with a differentiated companion

The companion may now be differentiated.  Its analytic order at a sample point is whatever it is —
possibly positive, since a differentiated jet does have zeros upstairs — and the point-dependent
integer grading absorbs it.

Separation is automatic for the binomial box: the order of the `a`-th monomial is
`a·(m+1) − (N−a)·V`, which is `a·(m+1+V) − N·V`, strictly monotone in `a`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The integer order form as a sum over all coordinates. -/
theorem integerBlowUpOrder_eq_sum_univ {n : ℕ} (d : Fin n → ℤ) (e : Fin n →₀ ℕ) :
    integerBlowUpOrder d e = ∑ k : Fin n, (e k : ℤ) * d k := by
  classical
  rw [integerBlowUpOrder, Finsupp.sum]
  refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
  have hz : e k = 0 := by
    by_contra hne
    exact hk (Finsupp.mem_support_iff.mpr hne)
  rw [hz]
  simp

theorem integerBlowUpOrder_fin_two (d : Fin 2 → ℤ) (e : Fin 2 →₀ ℕ) :
    integerBlowUpOrder d e = (e 0 : ℤ) * d 0 + (e 1 : ℤ) * d 1 := by
  rw [integerBlowUpOrder_eq_sum_univ, Fin.sum_univ_two]

/-- **The translated differentiated jet has finite analytic order.**  Were the order infinite the
jet would vanish identically on the convex strip `Im > −σ.im`, which it does not. -/
theorem analyticOrderAt_translate_jet_ne_top (θ : BoundedRealSequence) (r : ℕ) {σ ζ : ℂ}
    (hζ : -σ.im < ζ.im) :
    analyticOrderAt (fun w => iteratedDeriv r (movingCanonicalLogDerivative θ) (w + σ)) ζ ≠ ⊤ := by
  set U : Set ℂ := {w : ℂ | -σ.im < w.im} with hU
  have hUconv : Convex ℝ U := convex_halfSpace_im_gt (-σ.im)
  have hana : ∀ w ∈ U, AnalyticAt ℂ
      (fun v => iteratedDeriv r (movingCanonicalLogDerivative θ) (v + σ)) w := by
    intro w hw
    refine analyticAt_translate_jet r σ ?_
    have hw' : -σ.im < w.im := hw
    simp only [Complex.add_im]
    linarith
  obtain ⟨z₀, hz₀im, hz₀ne⟩ := exists_ne_zero_iteratedDeriv_movingCanonicalLogDerivative θ r
  have hw₀U : z₀ - σ ∈ U := by
    show -σ.im < (z₀ - σ).im
    simp only [Complex.sub_im]
    linarith
  intro htop
  have hev : (fun w => iteratedDeriv r (movingCanonicalLogDerivative θ) (w + σ))
      =ᶠ[𝓝 ζ] 0 := analyticOrderAt_eq_top.mp htop
  have hanaOn : AnalyticOnNhd ℂ
      (fun v => iteratedDeriv r (movingCanonicalLogDerivative θ) (v + σ)) U := hana
  have hzero := hanaOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hUconv.isPreconnected (show ζ ∈ U from hζ) hev
  have hval := hzero hw₀U
  simp only [Pi.zero_apply, sub_add_cancel] at hval
  exact hz₀ne hval


/-- The vanishing order of a translated differentiated jet at a point. -/
noncomputable def translateJetVanishingOrder (θ : BoundedRealSequence) (r : ℕ) (σ ζ : ℂ) : ℕ :=
  (analyticOrderAt (fun w => iteratedDeriv r (movingCanonicalLogDerivative θ) (w + σ)) ζ).toNat

/-- On the strip `Im > −σ.im` the recorded order is the analytic order. -/
theorem analyticOrderAt_translate_jet_eq (θ : BoundedRealSequence) (r : ℕ) {σ ζ : ℂ}
    (hζ : -σ.im < ζ.im) :
    analyticOrderAt (fun w => iteratedDeriv r (movingCanonicalLogDerivative θ) (w + σ)) ζ
      = ((translateJetVanishingOrder θ r σ ζ : ℕ) : ℕ∞) :=
  (ENat.coe_toNat (analyticOrderAt_translate_jet_ne_top θ r hζ)).symm

/-- **Separation in the binomial box costs nothing.**  The two exponents move oppositely, so the
order of the `a`-th monomial is `a·(d₀ − d₁) + N·d₁`, injective in `a` as soon as the two rates
differ. -/
theorem injective_integerBlowUpOrder_binomialJetBox (d : Fin 2 → ℤ) (N : ℕ) (hne : d 0 ≠ d 1) :
    Function.Injective fun a : Fin (N + 1) => integerBlowUpOrder d (binomialJetBox N a) := by
  intro a b hab
  simp only [integerBlowUpOrder_fin_two, binomialJetBox_apply_zero,
    binomialJetBox_apply_one] at hab
  have haN : (a : ℕ) ≤ N := Nat.lt_succ_iff.mp a.isLt
  have hbN : (b : ℕ) ≤ N := Nat.lt_succ_iff.mp b.isLt
  rw [Nat.cast_sub haN, Nat.cast_sub hbN] at hab
  have hkey : ((a : ℕ) : ℤ) * (d 0 - d 1) = ((b : ℕ) : ℤ) * (d 0 - d 1) := by linarith [hab]
  have hd : d 0 - d 1 ≠ 0 := sub_ne_zero.mpr hne
  have : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := mul_right_cancel₀ hd hkey
  exact Fin.ext (Nat.cast_injective this)

/-- **Point-dependent blow-up data for translated jets.**  Each sampled point supplies its own
companion orders; nothing is assumed uniform along the sampled set. -/
theorem pointwiseIntegerMultiBlowUpData_translateJets {κ : Type*} {n : ℕ}
    (θ : BoundedRealSequence) (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n) (V : ℂ → Fin n → ℕ)
    {S Z : Set ℂ} (exponent : κ → (Fin n →₀ ℕ)) (hZ : Z.Infinite)
    (hS : ∀ ζ ∈ Z, ∀ y : ℝ, 0 < y → ζ + (y : ℂ) * Complex.I ∈ S)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    (hfin : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      AnalyticAt ℂ (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ)
    (hV : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      analyticOrderAt (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ
        = ((V ζ k : ℕ) : ℕ∞))
    (hsep : ∀ ζ ∈ Z, Function.Injective fun a =>
      integerBlowUpOrder (integerTranslateJetRate m k₀ (V ζ)) (exponent a)) :
    PointwiseIntegerMultiBlowUpData S
      (fun k w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) Z exponent := by
  refine ⟨hZ, fun ζ hζ => ?_⟩
  obtain ⟨u, t, c, humem, htne, hu, ht, hcne, hlim⟩ :=
    exists_translateJetBlowUp_at θ m σ k₀ (V ζ) (hS ζ hζ) (hzero ζ hζ) (hfin ζ hζ) (hV ζ hζ)
  exact ⟨u, t, c, integerTranslateJetRate m k₀ (V ζ),
    humem, htne, hu, ht, hcne, hsep ζ hζ, hlim⟩

set_option maxHeartbeats 1000000 in
/-- **Unconditional, with a differentiated companion.**  For every parameter sequence, pair of
differentiation orders, degree budget and box size there is a node packet in the open upper
half-plane, with pairwise distinct nodes, on which the expanded evaluation map of the binomial box
in `(L^{(m)}, L^{(r)}(· + i))` is injective.

The companion is differentiated and does vanish upstairs; the point-dependent grading absorbs its
order, and separation of the box is automatic because the two exponents move oppositely. -/
theorem exists_row_packet_movingCanonicalDifferentiatedBox
    (θ : BoundedRealSequence) (m r q N : ℕ) :
    ∃ z : (Fin (N + 1) × Fin (q + 1)) → ℂ, (∀ b, 0 < (z b).im) ∧ Function.Injective z ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q 2 z (binomialJetBox N)
        (fun p => iteratedDeriv ((![m, r] : Fin 2 → ℕ) p.2) (movingCanonicalLogDerivative θ)
          (z p.1 + (![0, Complex.I] : Fin 2 → ℂ) p.2))).mulVec := by
  classical
  have hZinj : Function.Injective
      (fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - (![0, Complex.I] : Fin 2 → ℂ) 0)) := by
    intro p₁ p₂ hp
    simp only [Matrix.cons_val_zero, sub_zero] at hp
    exact movingCanonicalZero_injective θ (Complex.ofReal_injective hp)
  have hjet : (fun w => iteratedDeriv ((![m, r] : Fin 2 → ℕ) 1) (movingCanonicalLogDerivative θ)
      (w + (![0, Complex.I] : Fin 2 → ℂ) 1))
      = fun w => iteratedDeriv r (movingCanonicalLogDerivative θ) (w + Complex.I) := by
    norm_num
  have hreal : ∀ ζ ∈ (Set.range fun p : ℕ =>
      ((movingCanonicalZero θ p : ℂ) - (![0, Complex.I] : Fin 2 → ℂ) 0)), ζ.im = 0 := by
    rintro ζ ⟨p, rfl⟩
    simp
  refine exists_row_packet_of_linearIndependent_box (q := q) infinite_upperHalfPlane
    (fun k w => iteratedDeriv ((![m, r] : Fin 2 → ℕ) k) (movingCanonicalLogDerivative θ)
      (w + (![0, Complex.I] : Fin 2 → ℂ) k)) (binomialJetBox N) ?_ id Function.injective_id
  refine linearIndependent_restrict_expandedMonomialFamily_of_pointwiseIntegerMultiBlowUp
    (κ := Fin (N + 1)) (q := q) (S := upperHalfPlane)
    (Z := Set.range fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - (![0, Complex.I] : Fin 2 → ℂ) 0))
    (exponent := binomialJetBox N) ?_
  refine pointwiseIntegerMultiBlowUpData_translateJets (κ := Fin (N + 1)) (S := upperHalfPlane)
    θ (![m, r]) (![0, Complex.I]) 0
    (fun ζ => ![0, translateJetVanishingOrder θ r Complex.I ζ]) (binomialJetBox N)
    (Set.infinite_range_of_injective hZinj) ?_ ?_ ?_ ?_ ?_
  · intro ζ hζ y hy
    show 0 < (ζ + (y : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero, hreal ζ hζ, zero_add]
    exact hy
  · rintro ζ ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  · intro ζ hζ k hk
    have hk1 : k = 1 := by
      fin_cases k
      · exact absurd rfl hk
      · rfl
    subst hk1
    rw [hjet]
    refine analyticAt_translate_jet r Complex.I ?_
    simp [Complex.add_im, hreal ζ hζ]
  · intro ζ hζ k hk
    have hk1 : k = 1 := by
      fin_cases k
      · exact absurd rfl hk
      · rfl
    subst hk1
    rw [hjet]
    have him : -Complex.I.im < ζ.im := by rw [hreal ζ hζ]; norm_num
    rw [analyticOrderAt_translate_jet_eq θ r him]
    norm_num
  · intro ζ _
    refine injective_integerBlowUpOrder_binomialJetBox _ N ?_
    have h0 : integerTranslateJetRate (![m, r] : Fin 2 → ℕ) 0
        (![0, translateJetVanishingOrder θ r Complex.I ζ] : Fin 2 → ℕ) 0 = (m : ℤ) + 1 := by
      simp [integerTranslateJetRate]
    have h1 : integerTranslateJetRate (![m, r] : Fin 2 → ℕ) 0
        (![0, translateJetVanishingOrder θ r Complex.I ζ] : Fin 2 → ℕ) 1
          = -((translateJetVanishingOrder θ r Complex.I ζ : ℤ)) := by
      simp [integerTranslateJetRate]
    rw [h0, h1]
    have : (0 : ℤ) ≤ (translateJetVanishingOrder θ r Complex.I ζ : ℤ) := Int.natCast_nonneg _
    omega

end GaloisForLFunctions.HTGeometry
