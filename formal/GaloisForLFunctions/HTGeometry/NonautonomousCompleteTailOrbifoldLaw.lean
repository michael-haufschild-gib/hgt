import GaloisForLFunctions.HTGeometry.NonautonomousProjectiveTailCollapse
import GaloisForLFunctions.HTGeometry.ParabolicOrbifoldTwelveCharge

/-!
# The complete tail of a degree-expanding rational protocol

Assembling the budget laws: for a protocol whose accumulated degrees grow at least geometrically
and whose source singularity budgets are fixed, every sufficiently late phase is non-hyperbolic and
carries at most two genuinely non-orbifold fibres, its parabolic signature is frozen, and the
rotational holonomy of the frozen signature is a protocol-specific tensor charge of at most `6`
dividing `12`.

Twelve is optimal as a charge chosen before the protocol is known: the orders `4` and `6` both
occur among the parabolic sphere signatures, so any universal charge is divisible by their least
common multiple.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Twelve is the least universal charge.**  A weight that works for every parabolic sphere
signature is divisible by `12`, because the orders `4` and `6` both occur. -/
theorem twelve_dvd_of_forall_holonomyOrder_dvd {k : ℕ}
    (hk : ∀ s : ParabolicSphereSignature, s.holonomyOrder ∣ k) : 12 ∣ k := by
  have h4 : (4 : ℕ) ∣ k := hk .twoFourFour
  have h6 : (6 : ℕ) ∣ k := hk .twoThreeSix
  have hlcm : Nat.lcm 4 6 ∣ k := Nat.lcm_dvd h4 h6
  have h12 : Nat.lcm 4 6 = 12 := by decide
  rwa [h12] at hlcm

/-- Both extreme holonomy orders are realized, so no smaller positive universal charge works. -/
theorem exists_holonomyOrder_eq_four_and_six :
    (∃ s : ParabolicSphereSignature, s.holonomyOrder = 4) ∧
      ∃ s : ParabolicSphereSignature, s.holonomyOrder = 6 :=
  ⟨⟨.twoFourFour, rfl⟩, ⟨.twoThreeSix, rfl⟩⟩

/-- **The complete tail reduction of a degree-expanding rational protocol.**  Geometric growth of
the accumulated degrees against fixed source budgets forces every sufficiently late phase to be
non-hyperbolic with at most two exceptional worldlines, freezes the parabolic signature, and
produces a protocol-specific tensor charge of at most `6` dividing `12` which every phase's
holonomy order divides. -/
theorem completeTail_orbifold_reduction
    (prefixDegree badFiberCard : ℕ → ℕ) (sourceExceptionalCard exceptionalBudget : ℕ)
    (hyperbolic : ℕ → Prop) (signature : ℕ → ParabolicSphereSignature)
    (hdegree : ∀ n, 2 ^ n ≤ prefixDegree n)
    (hthreeBudget : ∀ n, 3 ≤ badFiberCard n → prefixDegree n + 2 ≤ sourceExceptionalCard)
    (hhyperbolicDegree : ∀ n, hyperbolic n → prefixDegree n ≤ 42 * exceptionalBudget)
    (hdiv : ∀ i, (signature i).holonomyOrder ∣ (signature (i + 1)).holonomyOrder)
    (hcompact : ∀ i, (signature i).isCompact = (signature (i + 1)).isCompact) :
    ∃ N charge,
      charge ≤ 6 ∧ charge ∣ 12 ∧
      (∀ i, (signature i).holonomyOrder ∣ charge) ∧
      ∀ n, N ≤ n →
        badFiberCard n ≤ 2 ∧ ¬ hyperbolic n ∧ signature n = signature N ∧
          (signature n).holonomyOrder = charge := by
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (projectiveTail_eventually_nonhyperbolic_with_twoPointSkeleton prefixDegree badFiberCard
      sourceExceptionalCard exceptionalBudget hyperbolic hdegree hthreeBudget hhyperbolicDegree)
  obtain ⟨N₂, hN₂⟩ := parabolicSphereSignature_eventually_constant signature hdiv hcompact
  obtain ⟨N₃, charge, hchargeEq, hcharge6, hcharge12, hchargeDvd, hN₃⟩ :=
    parabolicSphereTower_has_protocol_charge signature hdiv
  refine ⟨max (max N₁ N₂) N₃, charge, hcharge6, hcharge12, hchargeDvd, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ N₃)) hn
  have hn₂ : N₂ ≤ n := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ N₃)) hn
  have hn₃ : N₃ ≤ n := le_trans (le_max_right _ N₃) hn
  have hM₂ : N₂ ≤ max (max N₁ N₂) N₃ :=
    le_trans (le_max_right N₁ N₂) (le_max_left _ N₃)
  have hM₃ : N₃ ≤ max (max N₁ N₂) N₃ := le_max_right _ N₃
  obtain ⟨hbad, hhyp⟩ := hN₁ n hn₁
  refine ⟨hbad, hhyp, ?_, hN₃ n hn₃⟩
  rw [hN₂ n hn₂, ← hN₂ _ hM₂]

/-- **The frozen tail carries a single tensor charge.**  Beyond the freezing phase every signature
is the same and its holonomy order is the protocol charge, so the corresponding power of the
translation-invariant current descends at every late phase. -/
theorem completeTail_frozen_charge
    (signature : ℕ → ParabolicSphereSignature)
    (hdiv : ∀ i, (signature i).holonomyOrder ∣ (signature (i + 1)).holonomyOrder)
    (hcompact : ∀ i, (signature i).isCompact = (signature (i + 1)).isCompact) :
    ∃ N charge, 0 < charge ∧ charge ≤ 6 ∧ charge ∣ 12 ∧
      (∀ i, (signature i).holonomyOrder ∣ charge) ∧
      (∀ n, N ≤ n → signature n = signature N) ∧
      ∀ n, N ≤ n → (signature n).holonomyOrder = charge := by
  obtain ⟨N₂, hN₂⟩ := parabolicSphereSignature_eventually_constant signature hdiv hcompact
  obtain ⟨N₃, charge, hchargeEq, hcharge6, hcharge12, hchargeDvd, hN₃⟩ :=
    parabolicSphereTower_has_protocol_charge signature hdiv
  refine ⟨max N₂ N₃, charge, ?_, hcharge6, hcharge12, hchargeDvd, ?_, ?_⟩
  · rw [hchargeEq]
    exact ParabolicSphereSignature.holonomyOrder_pos _
  · intro n hn
    rw [hN₂ n (le_trans (le_max_left N₂ N₃) hn), ← hN₂ _ (le_max_left N₂ N₃)]
  · intro n hn
    exact hN₃ n (le_trans (le_max_right N₂ N₃) hn)

end GaloisForLFunctions.HTGeometry
