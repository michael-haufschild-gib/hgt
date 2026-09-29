import GaloisForLFunctions.HTGeometry.TwoLocalPauliReplicaJetDepthLaw

/-!
# Replica-height control of a full-source spectral-jet neighborhood

For each system size `n`, one positive constant `c` is chosen before every
replica order `r`. Ordered replica characters either vanish identically
because their multiplicities coincide, or have a fixed detector of order at
most `min (n + 1) (Nat.log 2 r + 2)` whose magnitude stays at least one on
the full Pauli coefficient ball of radius `c / (r + 1)`. The same ball lies
inside the genuine real characteristic-root chart.

The proof uses the logarithmic detector theorem, linear dependence of the
action on the integer character, total replica coefficient mass at most
`2*r`, and a common local derivative bound for finitely many elementary
jets. The perturbation argument is standard; it is not itself a new
physical principle.

The system-size dependence of `c` is not estimated. The source neighborhood
shrinks with replica order. This is not a high-probability assertion for an
ordinary local-Hamiltonian ensemble, nor an incidence-action, complete-circuit
exclusion, laboratory-time growth, or first-return theorem.
-/

open scoped BigOperators Topology Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry
noncomputable section

noncomputable local instance radiusBoolCubeFintype
    {I : Type*} [Fintype I] : Fintype (I → Bool) := Fintype.ofFinite _

private abbrev Detector (n : ℕ) := Σ i : Fin n, Finset {j : Fin n // j ≠ i}

private def elementaryAction (n : ℕ) (x : Fin n → Bool) :=
  commonReferencePauliAction (Pi.single x (1 : ℝ))

private def detectorJet {n : ℕ} (d : Detector n)
    (k : (Fin n → Bool) → ℝ) (p : PauliBoundedLabel n 2 → ℝ) : ℝ :=
  iteratedFDeriv ℝ (starSpectralJetWord d.2).length
    (commonReferencePauliAction k) p
    (fun j => starPauliDirectionMap d.1 (Pi.single ((starSpectralJetWord d.2).get j) 1))

private theorem pauliAction_basis_expansion {n : ℕ} (k : (Fin n → Bool) → ℝ) :
    commonReferencePauliAction k = fun p => ∑ x, k x • elementaryAction n x p := by
  classical
  have hs (x : Fin n → Bool) (p : PauliBoundedLabel n 2 → ℝ) :
      elementaryAction n x p =
        (commonReferenceSpectralBranch n x (commonReferencePauliMatrix n p)).re := by
    simp [elementaryAction, commonReferencePauliAction, commonReferenceChartAction,
      Pi.single_apply]
  funext p
  simp only [hs, smul_eq_mul, commonReferencePauliAction, commonReferenceChartAction]

private theorem detectorJet_basis_expansion {n : ℕ} (d : Detector n)
    (k : (Fin n → Bool) → ℝ) (p : PauliBoundedLabel n 2 → ℝ)
    (h : ∀ x, ContDiffAt ℝ (starSpectralJetWord d.2).length (elementaryAction n x) p) :
    detectorJet d k p = ∑ x, k x * detectorJet d (Pi.single x 1) p := by
  classical
  unfold detectorJet
  rw [pauliAction_basis_expansion k,
    iteratedFDeriv_fun_sum_apply (fun x _ => (h x).const_smul (k x))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [iteratedFDeriv_const_smul_apply' (h x)]
  rfl

/-- A source ball and a Lipschitz constant chosen before the real covector.
This controls the entire finite family of star-direction jets in full source space. -/
private theorem detectorJet_uniform_linear_variation (n : ℕ) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧
      ∀ (d : Detector n) (k : (Fin n → Bool) → ℝ)
        (p : PauliBoundedLabel n 2 → ℝ), p ∈ Metric.ball 0 R →
        |detectorJet d k p - detectorJet d k 0| ≤ (∑ x, |k x|) * C * ‖p‖ := by
  classical
  have hlocal (d : Detector n) (x : Fin n → Bool) :
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ p in 𝓝 (0 : PauliBoundedLabel n 2 → ℝ),
        |detectorJet d (Pi.single x 1) p - detectorJet d (Pi.single x 1) 0| ≤ C * ‖p‖ := by
    let dirs := fun j => starPauliDirectionMap d.1
      (Pi.single ((starSpectralJetWord d.2).get j) (1 : ℝ))
    have hd : DifferentiableAt ℝ (detectorJet d (Pi.single x 1)) 0 := by
      apply DifferentiableAt.comp
        (f := iteratedFDeriv ℝ (starSpectralJetWord d.2).length
          (commonReferencePauliAction (Pi.single x 1)))
        (g := ContinuousMultilinearMap.apply ℝ _ ℝ dirs) 0
      · exact (ContinuousMultilinearMap.apply ℝ _ ℝ dirs).differentiableAt
      · exact ((contDiffAt_commonReferencePauliAction (Pi.single x 1)).iteratedFDeriv_right
          (m := 1) (show (1 : WithTop ℕ∞) + (starSpectralJetWord d.2).length ≤ ⊤ from
            le_top)).differentiableAt_one
    obtain ⟨C, hC, hbound⟩ := hd.isBigO_sub.exists_pos
    exact ⟨C, hC, by simpa only [Real.norm_eq_abs, sub_zero] using hbound.bound⟩
  choose C hC hbound using hlocal
  let M : ℝ := 1 + ∑ d : Detector n, ∑ x : Fin n → Bool, C d x
  have hsum (d : Detector n) : 0 ≤ ∑ x : Fin n → Bool, C d x :=
    Finset.sum_nonneg (fun x _ => (hC d x).le)
  have hM : 0 < M := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun d _ => hsum d))
  have hCM (d : Detector n) (x : Fin n → Bool) : C d x ≤ M := by
    calc
      C d x ≤ ∑ y, C d y := Finset.single_le_sum
        (fun y _ => (hC d y).le) (Finset.mem_univ x)
      _ ≤ ∑ e : Detector n, ∑ y, C e y := Finset.single_le_sum
        (fun e _ => hsum e) (Finset.mem_univ d)
      _ ≤ M := le_add_of_nonneg_left zero_le_one
  have hbounds : ∀ᶠ p in 𝓝 (0 : PauliBoundedLabel n 2 → ℝ),
      ∀ (d : Detector n) (x : Fin n → Bool),
        |detectorJet d (Pi.single x 1) p - detectorJet d (Pi.single x 1) 0| ≤ M * ‖p‖ := by
    apply Filter.eventually_all.mpr
    intro d
    apply Filter.eventually_all.mpr
    intro x
    filter_upwards [hbound d x] with p hp
    exact hp.trans (mul_le_mul_of_nonneg_right (hCM d x) (norm_nonneg p))
  have hsmooth : ∀ᶠ p in 𝓝 (0 : PauliBoundedLabel n 2 → ℝ),
      ∀ (d : Detector n) (x : Fin n → Bool),
        ContDiffAt ℝ (starSpectralJetWord d.2).length (elementaryAction n x) p := by
    apply Filter.eventually_all.mpr
    intro d
    apply Filter.eventually_all.mpr
    intro x
    exact ((contDiffAt_commonReferencePauliAction (Pi.single x 1)).of_le
      (show ((starSpectralJetWord d.2).length : WithTop ℕ∞) ≤ ⊤ from le_top)).eventually
      (by simp)
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hbounds.and hsmooth)
  refine ⟨R, M, hR, hM, ?_⟩
  intro d k p hp
  have h0 (x : Fin n → Bool) :
      ContDiffAt ℝ (starSpectralJetWord d.2).length (elementaryAction n x) 0 :=
    (contDiffAt_commonReferencePauliAction (Pi.single x 1)).of_le le_top
  rw [detectorJet_basis_expansion d k p ((hball hp).2 d),
    detectorJet_basis_expansion d k 0 h0, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, |k x * detectorJet d (Pi.single x 1) p -
        k x * detectorJet d (Pi.single x 1) 0| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |k x| * |detectorJet d (Pi.single x 1) p -
        detectorJet d (Pi.single x 1) 0| := by simp only [← mul_sub, abs_mul]
    _ ≤ ∑ x, |k x| * (M * ‖p‖) := Finset.sum_le_sum
      (fun x _ => mul_le_mul_of_nonneg_left ((hball hp).1 d x) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

private theorem orderedReplica_coefficient_mass_le {n r : ℕ}
    (α β : Fin r → (Fin n → Bool)) :
    (∑ x, |(orderedReplicaMultiplicity α x : ℝ) - orderedReplicaMultiplicity β x|) ≤
      2 * r := by
  have ha := (Finset.mem_piAntidiag.mp (orderedReplicaMultiplicity_mem_piAntidiag α)).1
  have hb := (Finset.mem_piAntidiag.mp (orderedReplicaMultiplicity_mem_piAntidiag β)).1
  calc
    _ ≤ ∑ x, ((orderedReplicaMultiplicity α x : ℝ) + orderedReplicaMultiplicity β x) := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [sub_zero, zero_sub, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg (orderedReplicaMultiplicity α x) :
          (0 : ℝ) ≤ orderedReplicaMultiplicity α x),
        abs_of_nonneg (Nat.cast_nonneg (orderedReplicaMultiplicity β x) :
          (0 : ℝ) ≤ orderedReplicaMultiplicity β x)] using
        abs_sub_le (orderedReplicaMultiplicity α x : ℝ) 0 (orderedReplicaMultiplicity β x)
    _ = _ := by rw [Finset.sum_add_distrib, ← Nat.cast_sum, ← Nat.cast_sum, ha, hb]; ring

/-- One system-size constant controls all replica orders. Every nonzero ordered
replica character has a logarithmic-order detector throughout the full source
ball of radius `c / (r + 1)`, inside the genuine real spectral chart. -/
theorem pauliOrderedReplica_inverse_height_jet_detection (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ,
      (∀ p ∈ Metric.ball (0 : PauliBoundedLabel n 2 → ℝ) (c / (r + 1)),
        ∀ x : Fin n → Bool,
          matrixCharpolyRelation (commonReferencePauliMatrix n p,
            commonReferenceSpectralBranch n x (commonReferencePauliMatrix n p)) = 0 ∧
          (commonReferenceSpectralBranch n x (commonReferencePauliMatrix n p)).im = 0) ∧
      ∀ α β : Fin r → (Fin n → Bool),
      orderedReplicaMultiplicity α = orderedReplicaMultiplicity β ∨
        ∃ (i : Fin n) (S : Finset {j : Fin n // j ≠ i}),
          2 ^ S.card ≤ r ∧
          (starSpectralJetWord S).length ≤ min (n + 1) (Nat.log 2 r + 2) ∧
          ∀ p ∈ Metric.ball (0 : PauliBoundedLabel n 2 → ℝ) (c / (r + 1)),
            1 ≤ |iteratedFDeriv ℝ (starSpectralJetWord S).length
              (commonReferencePauliAction (fun x =>
                (orderedReplicaMultiplicity α x : ℝ) - orderedReplicaMultiplicity β x)) p
              (fun j => starPauliDirectionMap i
                (Pi.single ((starSpectralJetWord S).get j) 1))| := by
  classical
  obtain ⟨R, C, hR, hC, hvariation⟩ := detectorJet_uniform_linear_variation n
  obtain ⟨R₀, hR₀, hroots, _⟩ := pauliOrderedReplica_uniform_logarithmic_jet_detection n 0
  let c := min R₀ (min R (1 / (2 * C)))
  have htwoC : 0 < 2 * C := mul_pos zero_lt_two hC
  have hc : 0 < c := lt_min hR₀ (lt_min hR (div_pos zero_lt_one htwoC))
  have hcC : c * (2 * C) ≤ 1 := (le_div_iff₀ htwoC).mp
    ((min_le_right R₀ _).trans (min_le_right R _))
  refine ⟨c, hc, ?_⟩
  intro r
  have hr : (0 : ℝ) < (r : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) zero_lt_one
  have hsmall : c / (r + 1) ≤ c := div_le_self hc.le
    (le_add_of_nonneg_left (Nat.cast_nonneg r))
  refine ⟨?_, ?_⟩
  · intro p hp
    exact hroots p (Metric.ball_subset_ball (hsmall.trans (min_le_left R₀ _)) hp)
  intro α β
  rcases pauliOrderedReplica_logarithmic_jet_detection n r α β with heq | hjet
  · exact Or.inl heq
  obtain ⟨i, S, hmass, horder, horigin⟩ := hjet
  let k : (Fin n → Bool) → ℝ := fun x =>
    (orderedReplicaMultiplicity α x : ℝ) - orderedReplicaMultiplicity β x
  have htwo : (2 : ℝ) ≤ |detectorJet ⟨i, S⟩ k 0| := by
    have hpow : (1 : ℝ) ≤ 2 ^ S.card := one_le_pow₀ one_le_two
    rw [pow_succ] at horigin
    change 2 ≤ |iteratedFDeriv ℝ (starSpectralJetWord S).length
      (commonReferencePauliAction k) 0
      (fun j => starPauliDirectionMap i (Pi.single ((starSpectralJetWord S).get j) 1))|
    exact (le_mul_of_one_le_left zero_le_two hpow).trans horigin
  refine Or.inr ⟨i, S, hmass, horder, ?_⟩
  intro p hp
  have hpR : p ∈ Metric.ball 0 R := Metric.ball_subset_ball
    (hsmall.trans ((min_le_right R₀ _).trans (min_le_left R _))) hp
  have hpnorm : ‖p‖ ≤ c / (r + 1) := by
    exact (by simpa only [Metric.mem_ball, dist_zero_right] using hp :
      ‖p‖ < c / (r + 1)).le
  have hvar : |detectorJet ⟨i, S⟩ k p - detectorJet ⟨i, S⟩ k 0| ≤ 1 := by
    calc
      _ ≤ (∑ x, |k x|) * C * ‖p‖ := hvariation ⟨i, S⟩ k p hpR
      _ ≤ (2 * r) * C * (c / (r + 1)) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right (orderedReplica_coefficient_mass_le α β) hC.le)
          hpnorm (norm_nonneg p) (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg r)) hC.le)
      _ = (c * (2 * C)) * ((r : ℝ) / (r + 1)) := by ring
      _ ≤ 1 * 1 := mul_le_mul hcC ((div_le_one hr).mpr (le_add_of_nonneg_right zero_le_one))
        (div_nonneg (Nat.cast_nonneg r) hr.le) zero_le_one
      _ = 1 := one_mul 1
  have htriangle := abs_sub_le (detectorJet ⟨i, S⟩ k 0) (detectorJet ⟨i, S⟩ k p) 0
  rw [sub_zero, sub_zero, abs_sub_comm] at htriangle
  change 1 ≤ |detectorJet ⟨i, S⟩ k p|
  linarith only [htwo, hvar, htriangle]

end
end GaloisForLFunctions.HTGeometry
