import GaloisForLFunctions.HTGeometry.StrelitzJetCurveNewtonEdge

/-!
# Exhaustive numerical branch dichotomy for the Strelitz jet curve

Every selected root branch has one of two cofinal behaviours.  Either it is eventually nonzero,
in which case the Newton-slope and exact edge-root package applies, or it vanishes on a strictly
increasing cofinal subsequence.  In the latter case root proximity forces the observed second
logarithmic jet itself to tend to zero on that subsequence.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- Complete data asserted in the nonzero branch of the Strelitz Newton-edge extraction. -/
def HasStrelitzJetCurveNewtonEdgeLimit
    (S : MvPolynomial (Fin 2) ℂ) (u root : ℕ → ℂ) : Prop :=
  ∃ i ∈ (strelitzJetCurvePolynomial S).support,
    ∃ j ∈ (strelitzJetCurvePolynomial S).support, i ≠ j ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        Tendsto (fun k => strelitzJetCurveRootLogSlope u root (ns k)) atTop
          (nhds (strelitzJetCurveNewtonSlope S i j)) ∧
        (∀ k ∈ (strelitzJetCurvePolynomial S).support,
          strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) k ≤
            strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) i) ∧
        ∃ c : ℂ, c ≠ 0 ∧
          (strelitzJetCurveNewtonEdgePolynomial S
            (strelitzJetCurveNewtonSlope S i j)
            (strelitzJetCurveNewtonWeight S
              (strelitzJetCurveNewtonSlope S i j) i)).IsRoot c

/-- Every sequence is either eventually nonzero or has a strictly increasing subsequence of exact
zeros. -/
theorem eventually_ne_or_exists_strictMono_eq_zero (root : ℕ → ℂ) :
    (∀ᶠ n : ℕ in atTop, root n ≠ 0) ∨
      ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ k, root (ns k) = 0 := by
  classical
  by_cases hevent : ∀ᶠ n : ℕ in atTop, root n ≠ 0
  · exact Or.inl hevent
  · right
    have hfreq : ∃ᶠ n : ℕ in atTop, root n = 0 := by
      simpa using (Filter.not_eventually.mp hevent)
    have hunbounded : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ root n = 0 := by
      intro N
      obtain ⟨n, hnzero, hnN⟩ :=
        (hfreq.and_eventually (eventually_ge_atTop N)).exists
      exact ⟨n, hnN, hnzero⟩
    let pick : ℕ → ℕ := fun N => Classical.choose (hunbounded N)
    have hpick_ge : ∀ N, N ≤ pick N := fun N =>
      (Classical.choose_spec (hunbounded N)).1
    have hpick_zero : ∀ N, root (pick N) = 0 := fun N =>
      (Classical.choose_spec (hunbounded N)).2
    let ns : ℕ → ℕ := Nat.rec (pick 0) (fun _ previous => pick (previous + 1))
    have hstep : ∀ k, ns k < ns (k + 1) := by
      intro k
      change ns k < pick (ns k + 1)
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hpick_ge (ns k + 1))
    refine ⟨ns, strictMono_nat_of_lt_succ hstep, ?_⟩
    intro k
    cases k with
    | zero => exact hpick_zero 0
    | succ k => exact hpick_zero (ns k + 1)

/-- If exact selected roots vanish along a cofinal subsequence and remain asymptotically close to an
observed jet, that observed jet tends to zero on the same subsequence. -/
theorem tendsto_norm_zero_of_root_eq_zero_subsequence
    {v root : ℕ → ℂ} {ns : ℕ → ℕ} (hns : StrictMono ns)
    (hclose : Tendsto (fun n => ‖v n - root n‖) atTop (nhds 0))
    (hzero : ∀ k, root (ns k) = 0) :
    Tendsto (fun k => ‖v (ns k)‖) atTop (nhds 0) := by
  have hsub := hclose.comp hns.tendsto_atTop
  refine hsub.congr' (Filter.Eventually.of_forall fun k => ?_)
  simp [hzero k]

/-- **Exhaustive Strelitz branch dichotomy.**  An exact specialized-root sequence approaching the
observed second logarithmic jet either has the full nonzero Newton-edge package or has a cofinal
zero-root subsequence on which the observed jet tends to zero. -/
theorem strelitzJetCurve_newtonEdge_or_zeroBranch
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {u v root : ℕ → ℂ} (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hclose : Tendsto (fun n => ‖v n - root n‖) atTop (nhds 0)) :
    HasStrelitzJetCurveNewtonEdgeLimit S u root ∨
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        (∀ k, root (ns k) = 0) ∧
        Tendsto (fun k => ‖v (ns k)‖) atTop (nhds 0) := by
  rcases eventually_ne_or_exists_strictMono_eq_zero root with hne | ⟨ns, hns, hzero⟩
  · left
    exact exists_strelitzJetCurveNewtonEdgeRoot_tendsto_subsequence hS huTop hroot hne
  · right
    exact ⟨ns, hns, hzero,
      tendsto_norm_zero_of_root_eq_zero_subsequence hns hclose hzero⟩

end

end GaloisForLFunctions.HTGeometry
