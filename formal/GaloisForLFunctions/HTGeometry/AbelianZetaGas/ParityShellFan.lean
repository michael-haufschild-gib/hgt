import GaloisForLFunctions.HTGeometry.AbelianZetaGas.FermionicOrderDuality

/-!
# Odd/even RG shell fan

The bosonic condensation fan splits by depth parity.  Odd depths carry walls
`1, 1/3, 1/5, ...`; even depths are exactly the image of `delta_2` and carry
`1/2, 1/4, ...`.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Condensation walls carried by odd bosonic depths. -/
def oddDepthCondensationFan : Set ℝ :=
  {x | ∃ n : ℕ, x = 1 / ((2 * n + 1 : ℕ) : ℝ)}

/-- Condensation walls carried by even bosonic depths. -/
def evenDepthCondensationFan : Set ℝ :=
  {x | ∃ n : ℕ, x = 1 / ((2 * (n + 1) : ℕ) : ℝ)}

/-- Full bosonic mode-condensation fan. -/
def fullDepthCondensationFan : Set ℝ :=
  {x | ∃ g : ℕ, 1 ≤ g ∧ x = 1 / (g : ℝ)}

/-- Odd-depth wall: at or below `1/(2n+1)`, infinitely many exact-depth modes are occupied. -/
theorem oddDepth_infinite_exactDepth_eq_one
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ)
    (hwall : σ ≤ 1 / ((2 * n + 1 : ℕ) : ℝ)) :
    (AbelianZetaParameters.temperatureParameters σ hσ).gasMeasure
      {k | (localHitSet
        ((AbelianZetaParameters.temperatureParameters σ hσ).exactDepthEvent (2 * n + 1)) k).Infinite}
      = 1 := by
  exact AbelianZetaParameters.temperature_infinite_exactDepth_eq_one hσ (by omega) hwall

/-- Above an odd-depth wall, even the corresponding depth tail is finite almost surely. -/
theorem oddDepth_finite_depthTail_eq_one
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ)
    (hwall : 1 / ((2 * n + 1 : ℕ) : ℝ) < σ) :
    (AbelianZetaParameters.temperatureParameters σ hσ).gasMeasure
      {k | (localHitSet
        ((AbelianZetaParameters.temperatureParameters σ hσ).depthTailEvent (2 * n + 1)) k).Finite}
      = 1 := by
  exact AbelianZetaParameters.temperature_finite_depthTail_eq_one hσ (by omega) hwall

/-- Even-depth wall: at or below `1/(2n+2)`, infinitely many exact-depth modes are occupied. -/
theorem evenDepth_infinite_exactDepth_eq_one
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ)
    (hwall : σ ≤ 1 / ((2 * (n + 1) : ℕ) : ℝ)) :
    (AbelianZetaParameters.temperatureParameters σ hσ).gasMeasure
      {k | (localHitSet
        ((AbelianZetaParameters.temperatureParameters σ hσ).exactDepthEvent (2 * (n + 1))) k).Infinite}
      = 1 := by
  exact AbelianZetaParameters.temperature_infinite_exactDepth_eq_one hσ (by omega) hwall

/-- Above an even-depth wall, its whole depth tail is finite almost surely. -/
theorem evenDepth_finite_depthTail_eq_one
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ)
    (hwall : 1 / ((2 * (n + 1) : ℕ) : ℝ) < σ) :
    (AbelianZetaParameters.temperatureParameters σ hσ).gasMeasure
      {k | (localHitSet
        ((AbelianZetaParameters.temperatureParameters σ hσ).depthTailEvent (2 * (n + 1))) k).Finite}
      = 1 := by
  exact AbelianZetaParameters.temperature_finite_depthTail_eq_one hσ (by omega) hwall

/-- Even-depth modes are exactly the image of the RG depth dilation `delta_2`. -/
theorem range_depthDilation_two :
    Set.range (depthDilation 2) = {m : AbelianZetaMode | Even (AbelianZetaMode.depth m)} := by
  ext m
  constructor
  · rintro ⟨m₀, rfl⟩
    rw [Set.mem_setOf_eq, depth_depthDilation (by omega)]
    exact even_two_mul _
  · intro hm
    change Even (m.2 + 1) at hm
    rcases hm with ⟨j, hj⟩
    have hjpos : 1 ≤ j := by omega
    refine ⟨(m.1, j - 1), ?_⟩
    apply Prod.ext
    · rfl
    · simp only [depthDilation]
      omega

/-- Square-shell wall `1/2` belongs to the even fan. -/
theorem one_half_mem_evenDepthCondensationFan :
    (1 / 2 : ℝ) ∈ evenDepthCondensationFan := by
  exact ⟨0, by norm_num [evenDepthCondensationFan]⟩

/-- Square-shell wall `1/2` is absent from the odd-depth fan. -/
theorem one_half_not_mem_oddDepthCondensationFan :
    (1 / 2 : ℝ) ∉ oddDepthCondensationFan := by
  rintro ⟨n, hn⟩
  have hpos : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  field_simp at hn
  have hnat : 2 * n + 1 = (2 : ℕ) := by exact_mod_cast hn
  omega

/-- Both parity subfans are exactly the full bosonic fan split by depth parity. -/
theorem fullDepthCondensationFan_eq_union :
    fullDepthCondensationFan = oddDepthCondensationFan ∪ evenDepthCondensationFan := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    rcases Nat.even_or_odd g with heven | hodd
    · rcases heven with ⟨n, hn⟩
      have hnpos : 1 ≤ n := by omega
      right
      refine ⟨n - 1, ?_⟩
      congr 2
      omega
    · rcases hodd with ⟨n, hn⟩
      left
      exact ⟨n, by rw [hn]⟩
  · rintro (hx | hx)
    · rcases hx with ⟨n, rfl⟩
      exact ⟨2 * n + 1, by omega, rfl⟩
    · rcases hx with ⟨n, rfl⟩
      exact ⟨2 * (n + 1), by omega, rfl⟩

/-- Odd-depth dilation response, the order-organ calculus of the odd shell. -/
def oddDepthOrderResponse (σ σ' : EulerSigma) : ℂ :=
  oddDepthZetaPartition σ' / oddDepthZetaPartition σ

/-- Fermionic order response. -/
def fermionicOrderResponse (σ σ' : EulerSigma) : ℂ :=
  fermionicZetaPartition σ' / fermionicZetaPartition σ

/-- Equality of order laws transfers the entire odd-depth dilation response to fermions. -/
theorem fermionicOrderResponse_eq_oddDepth (σ σ' : EulerSigma) :
    fermionicOrderResponse σ σ' = oddDepthOrderResponse σ σ' := by
  rw [fermionicOrderResponse, oddDepthOrderResponse,
    fermionicZetaPartition_eq_oddDepth, fermionicZetaPartition_eq_oddDepth]

end

end GaloisForLFunctions.HTGeometry
