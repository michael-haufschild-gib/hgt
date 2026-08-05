import GaloisForLFunctions.HTGeometry.SpacedRayNodePacket
import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalFiniteJetSubmersion

/-!
# The even canonical carrier as a pole carrier

The moving canonical logarithmic derivative is `-logDeriv` of an entire product whose zeros are the
carrier's own real zeros.  It is therefore analytic at every point that is not one of them — the
half-plane hypotheses in the corpus were incidental to how the statement was first needed.

Since every zero exceeds `3/4`, the carrier is analytic on the whole half-plane `Re < 3/4`, and in
particular at every reflected zero `-ζ_p`.  That is exactly what the even carrier
`E θ z = L z - L (-z)` needs: near a zero the reflected summand stays bounded, so the even carrier
blows up with the same leading value as `L`.

The even carrier is then a `PoleCarrier`, and every full-rank result transfers to it unchanged.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **The carrier is analytic off its zeros.**  Nonvanishing of the canonical product on a
neighbourhood is what makes the logarithmic derivative analytic; no half-plane is involved. -/
theorem analyticAt_movingCanonicalLogDerivative_of_ne_zeros (θ : BoundedRealSequence) {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ (movingCanonicalZero θ n : ℂ)) :
    AnalyticAt ℂ (movingCanonicalLogDerivative θ) z := by
  have hproduct : AnalyticAt ℂ (movingCanonicalProduct θ) z :=
    movingCanonicalProduct_analytic θ z (Set.mem_univ z)
  have hproductNe : movingCanonicalProduct θ z ≠ 0 := by
    intro hzero
    obtain ⟨a, ha⟩ := (movingCanonicalProduct_eq_zero_iff θ z).mp hzero
    exact hz a ha
  have hlog : AnalyticAt ℂ (fun w => -logDeriv (movingCanonicalProduct θ) w) z := by
    have hquot : AnalyticAt ℂ
        (fun w => deriv (movingCanonicalProduct θ) w / movingCanonicalProduct θ w) z :=
      hproduct.deriv.div hproduct hproductNe
    change AnalyticAt ℂ
      (fun w => -(deriv (movingCanonicalProduct θ) w / movingCanonicalProduct θ w)) z
    exact hquot.neg
  refine hlog.congr ?_
  have hne : ∀ᶠ w in 𝓝 z, movingCanonicalProduct θ w ≠ 0 :=
    hproduct.continuousAt.eventually_ne hproductNe
  filter_upwards [hne] with w hw
  exact neg_logDeriv_movingCanonicalProduct_eq θ
    (fun a ha => hw ((movingCanonicalProduct_eq_zero_iff θ w).mpr ⟨a, ha⟩))

/-- Every zero exceeds `3/4`, so the carrier is analytic on the whole half-plane `Re < 3/4`. -/
theorem analyticAt_movingCanonicalLogDerivative_of_re_lt (θ : BoundedRealSequence) {z : ℂ}
    (hz : z.re < 3 / 4) : AnalyticAt ℂ (movingCanonicalLogDerivative θ) z := by
  refine analyticAt_movingCanonicalLogDerivative_of_ne_zeros θ fun n hn => ?_
  have hre : z.re = movingCanonicalZero θ n := by rw [hn]; simp
  have hlow := movingCanonicalZero_lower θ n
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [hre] at hz
  linarith

/-- The even canonical carrier is analytic on the open upper half-plane. -/
theorem analyticAt_movingEvenCanonicalCarrier (θ : BoundedRealSequence) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (movingEvenCanonicalCarrier θ) z := by
  have hneg : (-z).im ≠ 0 := by
    simp only [Complex.neg_im]
    exact neg_ne_zero.mpr (ne_of_gt hz)
  change AnalyticAt ℂ
    (fun w => movingCanonicalLogDerivative θ w - movingCanonicalLogDerivative θ (-w)) z
  exact (analyticAt_movingCanonicalLogDerivative θ hz).sub
    ((analyticAt_movingCanonicalLogDerivative_of_im_ne_zero θ hneg).comp (by fun_prop))

/-- Translated jets of the even carrier are analytic above the real axis. -/
theorem analyticAt_evenTranslate_jet (θ : BoundedRealSequence) (r : ℕ) (σ : ℂ) {ζ : ℂ}
    (hpos : 0 < (ζ + σ).im) :
    AnalyticAt ℂ (fun w => iteratedDeriv r (movingEvenCanonicalCarrier θ) (w + σ)) ζ := by
  have hinner : AnalyticAt ℂ (fun w : ℂ => w + σ) ζ := analyticAt_id.add analyticAt_const
  have houter : AnalyticAt ℂ (iteratedDeriv r (movingEvenCanonicalCarrier θ)) (ζ + σ) :=
    analyticAt_iteratedDeriv (analyticAt_movingEvenCanonicalCarrier θ hpos) r
  have hcomp : AnalyticAt ℂ
      ((iteratedDeriv r (movingEvenCanonicalCarrier θ)) ∘ (fun w : ℂ => w + σ)) ζ :=
    AnalyticAt.comp (g := iteratedDeriv r (movingEvenCanonicalCarrier θ)) houter hinner
  simpa [Function.comp_def] using hcomp

set_option maxHeartbeats 1000000 in
/-- **The even carrier blows up at every zero with the same leading value as the carrier.**  The
reflected summand is analytic at `-ζ_p`, hence bounded there, so it is annihilated by the vanishing
factor. -/
theorem tendsto_iteratedDeriv_translate_movingEvenCanonicalCarrier
    (θ : BoundedRealSequence) (p r : ℕ) (σ : ℂ) {u : ℕ → ℂ}
    (hupper : ∀ j, 0 < (u j + σ).im)
    (hu : Tendsto u atTop (𝓝 ((movingCanonicalZero θ p : ℂ) - σ))) :
    Tendsto (fun j => iteratedDeriv r (movingEvenCanonicalCarrier θ) (u j + σ) *
      (u j - ((movingCanonicalZero θ p : ℂ) - σ)) ^ (r + 1)) atTop
      (𝓝 (-((-1 : ℂ) ^ r * (r.factorial : ℂ)))) := by
  have hmain := tendsto_iteratedDeriv_translate_movingCanonicalLogDerivative θ p r σ hupper hu
  have hu' : Tendsto (fun j => u j + σ) atTop (𝓝 ((movingCanonicalZero θ p : ℂ))) := by
    have h := hu.add (tendsto_const_nhds (x := σ))
    simpa using h
  have hrefl : Tendsto (fun j => -((starRingEnd ℂ) (u j + σ))) atTop
      (𝓝 (-((movingCanonicalZero θ p : ℂ)))) := by
    have hconj : Tendsto (fun j => (starRingEnd ℂ) (u j + σ)) atTop
        (𝓝 ((starRingEnd ℂ) ((movingCanonicalZero θ p : ℂ)))) :=
      (Complex.continuous_conj.tendsto _).comp hu'
    have hpt : (starRingEnd ℂ) ((movingCanonicalZero θ p : ℂ))
        = ((movingCanonicalZero θ p : ℂ)) := by simp
    rw [hpt] at hconj
    exact hconj.neg
  have hana : AnalyticAt ℂ (iteratedDeriv r (movingCanonicalLogDerivative θ))
      (-((movingCanonicalZero θ p : ℂ))) := by
    refine analyticAt_iteratedDeriv (analyticAt_movingCanonicalLogDerivative_of_re_lt θ ?_) r
    have hpos := movingCanonicalZero_pos θ p
    simp only [Complex.neg_re, Complex.ofReal_re]
    linarith
  have hjetlim : Tendsto (fun j => iteratedDeriv r (movingCanonicalLogDerivative θ)
      (-((starRingEnd ℂ) (u j + σ)))) atTop
      (𝓝 (iteratedDeriv r (movingCanonicalLogDerivative θ)
        (-((movingCanonicalZero θ p : ℂ))))) :=
    hana.continuousAt.tendsto.comp hrefl
  have htz : Tendsto (fun j => u j - ((movingCanonicalZero θ p : ℂ) - σ)) atTop (𝓝 0) := by
    have h := hu.sub (tendsto_const_nhds (x := ((movingCanonicalZero θ p : ℂ) - σ)))
    simpa using h
  have htpow : Tendsto (fun j => (u j - ((movingCanonicalZero θ p : ℂ) - σ)) ^ (r + 1)) atTop
      (𝓝 0) := by
    have h := htz.pow (r + 1)
    simpa using h
  have hsecond : Tendsto (fun j => ((-1 : ℂ) ^ r *
      ((starRingEnd ℂ) (iteratedDeriv r (movingCanonicalLogDerivative θ)
        (-((starRingEnd ℂ) (u j + σ)))))) *
      (u j - ((movingCanonicalZero θ p : ℂ) - σ)) ^ (r + 1)) atTop (𝓝 0) := by
    have hc : Tendsto (fun j => (starRingEnd ℂ) (iteratedDeriv r (movingCanonicalLogDerivative θ)
        (-((starRingEnd ℂ) (u j + σ))))) atTop
        (𝓝 ((starRingEnd ℂ) (iteratedDeriv r (movingCanonicalLogDerivative θ)
          (-((movingCanonicalZero θ p : ℂ)))))) :=
      (Complex.continuous_conj.tendsto _).comp hjetlim
    have h := (hc.const_mul ((-1 : ℂ) ^ r)).mul htpow
    simpa using h
  have hsplit : ∀ j, iteratedDeriv r (movingCanonicalLogDerivative θ) (u j + σ) *
      (u j - ((movingCanonicalZero θ p : ℂ) - σ)) ^ (r + 1) -
      ((-1 : ℂ) ^ r * ((starRingEnd ℂ) (iteratedDeriv r (movingCanonicalLogDerivative θ)
        (-((starRingEnd ℂ) (u j + σ)))))) *
        (u j - ((movingCanonicalZero θ p : ℂ) - σ)) ^ (r + 1)
      = iteratedDeriv r (movingEvenCanonicalCarrier θ) (u j + σ) *
        (u j - ((movingCanonicalZero θ p : ℂ) - σ)) ^ (r + 1) := by
    intro j
    rw [iteratedDeriv_movingEvenCanonicalCarrier θ r (hupper j)]
    ring
  have hlim := hmain.sub hsecond
  rw [sub_zero] at hlim
  exact hlim.congr hsplit

/-- The even canonical carrier, as a pole carrier. -/
noncomputable def movingEvenCanonicalPoleCarrier (θ : BoundedRealSequence) : PoleCarrier where
  carrier := movingEvenCanonicalCarrier θ
  pole := movingCanonicalZero θ
  gap := by
    intro a b _
    have h1 := movingCanonicalZero_lower θ b
    have h2 := movingCanonicalZero_upper θ a
    linarith
  analyticJet := fun r σ _ h => analyticAt_evenTranslate_jet θ r σ h
  jetBlowUp := fun p r σ _ hupper hu =>
    ⟨-((-1 : ℂ) ^ r * (r.factorial : ℂ)), jetLeadingValue_ne_zero r,
      tendsto_iteratedDeriv_translate_movingEvenCanonicalCarrier θ p r σ hupper hu⟩

@[simp] theorem movingEvenCanonicalPoleCarrier_carrier (θ : BoundedRealSequence) :
    (movingEvenCanonicalPoleCarrier θ).carrier = movingEvenCanonicalCarrier θ := rfl

@[simp] theorem movingEvenCanonicalPoleCarrier_pole (θ : BoundedRealSequence) :
    (movingEvenCanonicalPoleCarrier θ).pole = movingCanonicalZero θ := rfl


/-- **Unconditional, for the even carrier.**  Every condition of the even translation-rank interface
is met by one node packet: pairwise distinct nodes, a collision-free row-by-shift family, every
shifted node in the open upper half-plane, and full expanded rank of the height box.

Nothing new is proved here — the even carrier is a `PoleCarrier`, so the general theorem applies. -/
theorem exists_row_packet_integerHeights_movingEvenCanonical
    (θ : BoundedRealSequence) (M n q N : ℕ) (m : Fin (M + 1) → ℕ)
    (height : Fin (M + 1) → Fin (n + 1)) :
    ∃ z : (Fin (N + 1) × Fin (q + 1)) → ℂ,
      Function.Injective z ∧
      Function.Injective (fun x : (Fin (N + 1) × Fin (q + 1)) × Fin (n + 1) =>
        z x.1 + integerHeightShift n x.2) ∧
      (∀ x : (Fin (N + 1) × Fin (q + 1)) × Fin (n + 1),
        0 < (z x.1 + integerHeightShift n x.2).im) ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q (M + 1) z
        (integerHeightBox height N)
        (fun p => iteratedDeriv (m p.2) (movingEvenCanonicalCarrier θ)
          (z p.1 + integerHeightShift n (groupHeightIdx height p.2)))).mulVec :=
  (movingEvenCanonicalPoleCarrier θ).exists_row_packet_integerHeights M n q N m height

end GaloisForLFunctions.HTGeometry
