import GaloisForLFunctions.HTGeometry.TripticJetAtomShift
import GaloisForLFunctions.HTGeometry.EllipticHypertranscendenceFreeProof
import GaloisForLFunctions.HTGeometry.MeromorphicFieldRealization
import GaloisForLFunctions.HTGeometry.EllipticMeroFieldDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.EllipticCompositumRationalBase
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicAntiderivative
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentLeading
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentDerivative

/-!
# The jets of a line atom are differentially algebraic

A line atom is `1`-periodic everywhere and changes by the constant `-2πi` under a quasiperiod step,
so every jet of positive order is periodic for the full lattice `ℤ + ℤσ` off the atom's poles.  The
poles are separated — two distinct points of the lattice are at distance at least `min 1 (Im σ)` —
so the periodicity holds on every punctured neighbourhood, hence for the canonical meromorphic
normal form everywhere.  A lattice-periodic normal form satisfies an algebraic differential
equation.

* `dist_atomPoleSet_ge` — the separation of the poles;
* `eventually_nhdsNE_notMem_atomPoleSet`;
* `periodic_toMeromorphicNFOn_jetAtom_succ` — both periods;
* `differentiallyAlgebraic_toMeromorphicNFOn_jetAtom_succ`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {σ : ℂ}

/-- **A nonzero point of the lattice `ℤ + ℤσ` has norm at least `min 1 (Im σ)`.** -/
theorem norm_lattice_ge (hσ : 0 < σ.im) {m n : ℤ} (hmn : ¬(m = 0 ∧ n = 0)) :
    min 1 σ.im ≤ ‖(m : ℂ) + (n : ℂ) * σ‖ := by
  by_cases hn : n = 0
  · have hm : m ≠ 0 := by
      intro h
      exact hmn ⟨h, hn⟩
    have hval : ((m : ℂ) + (n : ℂ) * σ) = (m : ℂ) := by
      rw [hn]
      push_cast
      ring
    rw [hval]
    have h1 : (1 : ℝ) ≤ ‖(m : ℂ)‖ := by
      have hm1 : (1 : ℤ) ≤ |m| := by
        rcases lt_or_gt_of_ne hm with h | h
        · rw [abs_of_neg h]; omega
        · rw [abs_of_pos h]; omega
      have hcast : (1 : ℝ) ≤ |(m : ℝ)| := by
        have h := (Int.cast_le (R := ℝ)).mpr hm1
        rwa [Int.cast_one, Int.cast_abs] at h
      simpa using hcast
    exact le_trans (min_le_left _ _) h1
  · have him : ((m : ℂ) + (n : ℂ) * σ).im = (n : ℝ) * σ.im := by
      simp
    have h1 : σ.im ≤ |((m : ℂ) + (n : ℂ) * σ).im| := by
      rw [him, abs_mul]
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have hn1' : (1 : ℤ) ≤ |n| := by
          rcases lt_or_gt_of_ne hn with h | h
          · rw [abs_of_neg h]; omega
          · rw [abs_of_pos h]; omega
        have h := (Int.cast_le (R := ℝ)).mpr hn1'
        rwa [Int.cast_one, Int.cast_abs] at h
      have habs : |σ.im| = σ.im := abs_of_pos hσ
      rw [habs]
      nlinarith [hσ.le]
    exact le_trans (min_le_right _ _) (le_trans h1 (Complex.abs_im_le_norm _))

/-- **Two distinct poles of a line atom are separated.** -/
theorem dist_atomPoleSet_ge (hσ : 0 < σ.im) {q z w : ℂ} (hz : z ∈ atomPoleSet σ q)
    (hw : w ∈ atomPoleSet σ q) (hzw : z ≠ w) : min 1 σ.im ≤ dist z w := by
  obtain ⟨m, n, rfl⟩ := hz
  obtain ⟨m', n', rfl⟩ := hw
  have hne : ¬((m - m' : ℤ) = 0 ∧ (n - n' : ℤ) = 0) := by
    rintro ⟨h1, h2⟩
    apply hzw
    have hm : m = m' := by omega
    have hn : n = n' := by omega
    rw [hm, hn]
  have hval : (q + thetaHalfPeriod σ + (m : ℂ) + (n : ℂ) * σ)
      - (q + thetaHalfPeriod σ + (m' : ℂ) + (n' : ℂ) * σ)
      = ((m - m' : ℤ) : ℂ) + ((n - n' : ℤ) : ℂ) * σ := by
    push_cast
    ring
  rw [Complex.dist_eq, hval]
  exact norm_lattice_ge hσ hne

/-- **The poles of a line atom are isolated:** on every punctured neighbourhood the atom is
eventually regular. -/
theorem eventually_nhdsNE_notMem_atomPoleSet (hσ : 0 < σ.im) (q z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, w ∉ atomPoleSet σ q := by
  by_cases hz : z ∈ atomPoleSet σ q
  · have hr : 0 < min 1 σ.im := lt_min one_pos hσ
    have hball : Metric.ball z (min 1 σ.im) ∈ 𝓝 z := Metric.ball_mem_nhds z hr
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with w hw hwne hmem
    have hdist : min 1 σ.im ≤ dist w z := dist_atomPoleSet_ge hσ hmem hz hwne
    rw [Metric.mem_ball] at hw
    exact absurd hw (not_lt.mpr hdist)
  · have hopen := isOpen_compl_atomPoleSet hσ q
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hz)] with w hw
    exact hw

/-- **A meromorphic function is not differentiable at a point where it is not analytic.**  It is
analytic on a punctured neighbourhood, so differentiability at the centre would make it
differentiable on a whole neighbourhood, hence analytic. -/
theorem not_differentiableAt_of_not_analyticAt {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (hna : ¬ AnalyticAt ℂ f z) : ¬ DifferentiableAt ℂ f z := by
  intro hdiff
  refine hna ?_
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hpunct : ∀ᶠ y in 𝓝[≠] z, DifferentiableAt ℂ f y :=
    hf.eventually_analyticAt.mono fun _ hy ↦ hy.differentiableAt
  rw [eventually_nhdsWithin_iff] at hpunct
  filter_upwards [hpunct] with y hy
  by_cases hyz : y = z
  · rw [hyz]
    exact hdiff
  · exact hy hyz

/-- **A pole stays a pole under differentiation.**  The leading Laurent coefficient of the
derivative is the order times the leading coefficient of the function. -/
theorem meromorphicOrderAt_deriv_neg {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z)
    (hord : meromorphicOrderAt f z < 0) : meromorphicOrderAt (deriv f) z < 0 := by
  have hne : meromorphicOrderAt f z ≠ ⊤ := by
    intro h
    rw [h] at hord
    exact absurd hord (by simp)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  have hnneg : n < 0 := by
    rw [← hn] at hord
    exact_mod_cast hord
  have hlead : laurentCoeff f z n ≠ 0 := laurentCoeff_leading_ne_zero hnneg hf hn.symm
  have hcoeff : laurentCoeff (deriv f) z (n - 1) = (n : ℂ) * laurentCoeff f z n := by
    rw [laurentCoeff_deriv hf (n - 1)]
    congr 1
    · push_cast
      ring
    · congr 1
      ring
  refine meromorphicOrderAt_neg_of_laurentCoeff_ne_zero hf.deriv (ℓ := n - 1) (by omega) ?_
  rw [hcoeff]
  exact mul_ne_zero (by exact_mod_cast hnneg.ne) hlead

/-- Punctured agreement passes to derivatives. -/
theorem eventuallyEq_deriv_of_eventuallyEq_nhdsNE {F f : ℂ → ℂ} {z : ℂ}
    (h : F =ᶠ[𝓝[≠] z] f) : deriv F =ᶠ[𝓝[≠] z] deriv f := by
  rw [Filter.eventuallyEq_iff_exists_mem] at h ⊢
  obtain ⟨s, hs, hEq⟩ := h
  rw [mem_nhdsWithin] at hs
  obtain ⟨u, hu, hzu, hsub⟩ := hs
  refine ⟨u ∩ {z}ᶜ, mem_nhdsWithin.mpr ⟨u, hu, hzu, fun y hy ↦ hy⟩, fun y hy ↦ ?_⟩
  have hopen : IsOpen (u ∩ {z}ᶜ) := hu.inter isOpen_compl_singleton
  have hev : F =ᶠ[𝓝 y] f := by
    filter_upwards [hopen.mem_nhds hy] with w hw
    exact hEq (hsub hw)
  exact hev.deriv_eq

/-- **Differentiation commutes with the canonical normal form.**  Off the poles both sides are the
derivative of the function; at a pole the normal form is not differentiable, so its derivative is
the junk value `0`, which is exactly the normal-form value of the derivative there. -/
theorem deriv_toMeromorphicNFOn (f : ℂ → ℂ) (hf : MeromorphicOn f (Set.univ : Set ℂ)) :
    deriv (toMeromorphicNFOn f (Set.univ : Set ℂ))
      = toMeromorphicNFOn (deriv f) (Set.univ : Set ℂ) := by
  have hfd : MeromorphicOn (deriv f) (Set.univ : Set ℂ) := fun z _ ↦ (hf z (Set.mem_univ z)).deriv
  set F : ℂ → ℂ := toMeromorphicNFOn f (Set.univ : Set ℂ) with hFdef
  set G : ℂ → ℂ := toMeromorphicNFOn (deriv f) (Set.univ : Set ℂ) with hGdef
  have hNFF : MeromorphicNFOn F (Set.univ : Set ℂ) := meromorphicNFOn_toMeromorphicNFOn _ _
  have hNFG : MeromorphicNFOn G (Set.univ : Set ℂ) := meromorphicNFOn_toMeromorphicNFOn _ _
  funext z
  have hFf : F =ᶠ[𝓝[≠] z] f := hf.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have hGd : G =ᶠ[𝓝[≠] z] deriv f := hfd.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have hFord : meromorphicOrderAt F z = meromorphicOrderAt f z :=
    meromorphicOrderAt_congr hFf
  rcases le_or_gt 0 (meromorphicOrderAt f z) with hord | hord
  · have hFan : AnalyticAt ℂ F z :=
      (hNFF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hFord ▸ hord)
    have hdFG : deriv F =ᶠ[𝓝[≠] z] G :=
      ((eventuallyEq_deriv_of_eventuallyEq_nhdsNE hFf).trans hGd.symm)
    have hGord : 0 ≤ meromorphicOrderAt G z := by
      rw [← meromorphicOrderAt_congr hdFG]
      exact hFan.deriv.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr hFan.deriv
    have hGan : AnalyticAt ℂ G z :=
      (hNFG (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hGord
    exact (eventuallyEq_nhds_of_nhdsNE_of_continuousAt hdFG hFan.deriv.continuousAt
      hGan.continuousAt).eq_of_nhds
  · have hFneg : meromorphicOrderAt F z < 0 := hFord ▸ hord
    have hFna : ¬ AnalyticAt ℂ F z := fun hcon ↦
      absurd ((hNFF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mpr hcon)
        (not_le.mpr hFneg)
    have hGneg : meromorphicOrderAt G z < 0 := by
      rw [hGdef, meromorphicOrderAt_toMeromorphicNFOn hfd (Set.mem_univ z)]
      exact meromorphicOrderAt_deriv_neg (hf z (Set.mem_univ z)) hord
    rw [deriv_zero_of_not_differentiableAt
        (not_differentiableAt_of_not_analyticAt (hNFF.meromorphicOn z (Set.mem_univ z)) hFna),
      eq_zero_of_meromorphicOrderAt_neg (hNFG (Set.mem_univ z)) hGneg]

section

variable (σ q : ℂ)

/-- Jets of a line atom are meromorphic on the plane. -/
theorem meromorphicOn_jetAtom (hσ : 0 < σ.im) (j : ℕ) :
    MeromorphicOn (jetAtom σ q j) (Set.univ : Set ℂ) := fun z _ ↦ meromorphicAt_jetAtom hσ q j z

/-- The normal form of a positive-order jet is `1`-periodic. -/
theorem periodic_toMeromorphicNFOn_jetAtom_one (hσ : 0 < σ.im) (j : ℕ) :
    Function.Periodic (toMeromorphicNFOn (jetAtom σ q (j + 1)) (Set.univ : Set ℂ)) 1 :=
  periodic_toMeromorphicNFOn_of_eventually_punctured_meromorphic
    (meromorphicOn_jetAtom σ q hσ (j + 1)) 1
    fun _ ↦ Filter.Eventually.of_forall fun w ↦ jetAtom_periodic_one σ q (j + 1) w

/-- The normal form of a positive-order jet is `σ`-periodic. -/
theorem periodic_toMeromorphicNFOn_jetAtom_sigma (hσ : 0 < σ.im) (j : ℕ) :
    Function.Periodic (toMeromorphicNFOn (jetAtom σ q (j + 1)) (Set.univ : Set ℂ)) σ :=
  periodic_toMeromorphicNFOn_of_eventually_punctured_meromorphic
    (meromorphicOn_jetAtom σ q hσ (j + 1)) σ
    fun z ↦ (eventually_nhdsNE_notMem_atomPoleSet hσ q z).mono fun _ hw ↦
      jetAtom_shift_succ hσ q j hw

/-- **Every positive-order jet of a line atom is differentially algebraic.**  Its normal form is
periodic for the full lattice `ℤ + ℤσ`. -/
theorem differentiallyAlgebraic_toMeromorphicNFOn_jetAtom_succ (hσ : 0 < σ.im) (j : ℕ) :
    DifferentiallyAlgebraic (toMeromorphicNFOn (jetAtom σ q (j + 1)) (Set.univ : Set ℂ)) := by
  have hindep : LinearIndependent ℝ ![(1 : ℂ), σ] := linearIndependent_one_of_im_pos hσ
  set F : ℂ → ℂ := toMeromorphicNFOn (jetAtom σ q (j + 1)) (Set.univ : Set ℂ) with hFdef
  have hNF : MeromorphicNFOn F (Set.univ : Set ℂ) := meromorphicNFOn_toMeromorphicNFOn _ _
  have hlat : ∀ p ∈ (⟨1, σ, hindep⟩ : PeriodPair).lattice, Function.Periodic F p := by
    intro p hp
    refine periodic_of_mem_span_range ![(1 : ℂ), σ] (fun i ↦ ?_) p ?_
    · fin_cases i
      · exact periodic_toMeromorphicNFOn_jetAtom_one σ q hσ j
      · exact periodic_toMeromorphicNFOn_jetAtom_sigma σ q hσ j
    · rw [range_cons_two]
      exact hp
  exact differentiallyAlgebraic_of_lattice_periodic_meromorphicNF ⟨1, σ, hindep⟩ hNF hlat

/-- The derivative of a jet of a line atom is the next jet. -/
theorem deriv_jetAtom (j : ℕ) : deriv (jetAtom σ q j) = jetAtom σ q (j + 1) := by
  show deriv (iteratedDeriv j (lineAtom σ q)) = iteratedDeriv (j + 1) (lineAtom σ q)
  rw [iteratedDeriv_succ]

/-- **Every jet of a line atom, the atom itself included, is differentially algebraic.**  The atom
is not lattice-periodic — a quasiperiod step changes it by `-2πi` — but its derivative is, and
differential algebraicity passes to antiderivatives. -/
theorem differentiallyAlgebraic_toMeromorphicNFOn_jetAtom (hσ : 0 < σ.im) (j : ℕ) :
    DifferentiallyAlgebraic (toMeromorphicNFOn (jetAtom σ q j) (Set.univ : Set ℂ)) := by
  cases j with
  | succ k => exact differentiallyAlgebraic_toMeromorphicNFOn_jetAtom_succ σ q hσ k
  | zero =>
      refine differentiallyAlgebraic_of_deriv ?_
      rw [deriv_toMeromorphicNFOn _ (meromorphicOn_jetAtom σ q hσ 0), deriv_jetAtom]
      exact differentiallyAlgebraic_toMeromorphicNFOn_jetAtom_succ σ q hσ 0

end

end

end GaloisForLFunctions.HTGeometry
