import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.EnvelopeTransversality

/-! # Strict operator improvement from matched active readings -/

open Filter Set
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
open AccuracyScales.TenthPlateau
noncomputable section
private abbrev Mat (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- A second tangent with the same readings on every maximizing vector
inherits strict descent. The gain covers any prescribed quadratic error,
as required when the second tangent is realized by a product of gates. -/
theorem matched_descent {N : ℕ} (X T S : Mat N) (hX : 0<‖X‖) (hgain : ‖X+T‖<‖X‖)
    (hmatch : ∀ ψ∈maxRightSingularSphere X,
      (inner ℂ (matAct X ψ) (matAct S ψ)).re=(inner ℂ (matAct X ψ) (matAct T ψ)).re)
    (B : ℝ) :
    ∃ r>(0:ℝ), ‖X+(r:ℂ) • S‖+B*r^2<‖X‖ := by
  let g := fun ψ => (inner ℂ (matAct X ψ) (matAct S ψ)).re/‖X‖
  have hbound : sSup (g '' maxRightSingularSphere X)≤‖X+T‖-‖X‖ := by
    apply csSup_le ((nonempty_maxRightSingularSphere X).image g)
    rintro _ ⟨ψ,hψ,rfl⟩
    have hh := opNorm_add_smul_ge_of_mem_maxRightSingularSphere hX hψ T 1
    simp only [Complex.ofReal_one,one_smul,one_mul] at hh
    change (inner ℂ (matAct X ψ) (matAct S ψ)).re/‖X‖≤_
    rw [hmatch ψ hψ]
    linarith only [hh]
  have hlim := (tendsto_opNorm_directionalDeriv hX S).2
  have hc : Tendsto (fun r : ℝ => B*r) (𝓝[>] 0) (𝓝 0) := by
    simpa only [id_eq,mul_zero] using (tendsto_const_nhds (x:=B)).mul
      (tendsto_id.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds))
  have hn := (hlim.add hc).eventually_lt_const
    (show sSup (g '' maxRightSingularSphere X)+0<0 by linarith only [hbound,hgain])
  have hpos : ∀ᶠ r in 𝓝[>] (0:ℝ), 0<r := self_mem_nhdsWithin
  obtain ⟨r,hr',h⟩ := (hpos.and hn).exists
  change (‖X+(r:ℂ) • S‖-‖X‖)/r+B*r<0 at h
  have hlin := (div_lt_iff₀ hr').mp (show (‖X+(r:ℂ) • S‖-‖X‖)/r< -(B*r) by linarith only [h])
  exact ⟨r,hr',by nlinarith only [hlin]⟩

#print axioms matched_descent
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
