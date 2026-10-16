import GaloisForLFunctions.RHTower.PaperThetaSpatialJets
import GaloisForLFunctions.RHTower.PaperThetaConfluentCut

/-! # One literal differential action on the theta jet module

The endpoint value is recovered from the function itself. Its subtraction
homogenizes the native source equation. The resulting action is linear on
the actual right-tail jet space and keeps every confluent predecessor.
-/

noncomputable section
open Complex Set Filter Topology

namespace RHTower.PaperThetaEndpoint

def thetaRightJetSpace : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ (range fun p : ℂ × ℕ => flatParameterJet p.2 p.1)

theorem flatParameterJet_mem_thetaRightJetSpace (n : ℕ) (z : ℂ) :
    flatParameterJet n z ∈ thetaRightJetSpace :=
  Submodule.subset_span (mem_range_self (z, n))

private theorem rightJet_regular (f : ℝ → ℂ) (hf : f ∈ thetaRightJetSpace) :
    Differentiable ℝ f ∧ ∃ c : ℂ, Tendsto f atTop (𝓝 c) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨⟨z, n⟩, rfl⟩ := hf
      exact ⟨differentiable_flatParameterJet n z, _, tendsto_flatParameterJet_atTop n z⟩
  | zero => exact ⟨differentiable_const _, 0, tendsto_const_nhds⟩
  | add f g _ _ hf hg =>
      obtain ⟨a, ha⟩ := hf.2
      obtain ⟨b, hb⟩ := hg.2
      exact ⟨hf.1.add hg.1, a+b, ha.add hb⟩
  | smul c f _ hf =>
      obtain ⟨a, ha⟩ := hf.2
      exact ⟨hf.1.const_mul c, c*a, ha.const_mul c⟩

def thetaTailTrace (f : ℝ → ℂ) : ℂ := limUnder atTop f

theorem thetaTailTrace_flatParameterJet (n : ℕ) (z : ℂ) :
    thetaTailTrace (flatParameterJet n z) = parameterEndpointTrace n :=
  (tendsto_flatParameterJet_atTop n z).limUnder_eq

private theorem rightJet_tendsto (f : ℝ → ℂ) (hf : f ∈ thetaRightJetSpace) :
    Tendsto f atTop (𝓝 (thetaTailTrace f)) := by
  obtain ⟨c, hc⟩ := (rightJet_regular f hf).2
  simpa only [thetaTailTrace, hc.limUnder_eq] using hc

private theorem tailTrace_add (f g : ℝ → ℂ)
    (hf : f ∈ thetaRightJetSpace) (hg : g ∈ thetaRightJetSpace) :
    thetaTailTrace (f+g) = thetaTailTrace f + thetaTailTrace g :=
  ((rightJet_tendsto f hf).add (rightJet_tendsto g hg)).limUnder_eq

private theorem tailTrace_smul (c : ℂ) (f : ℝ → ℂ) (hf : f ∈ thetaRightJetSpace) :
    thetaTailTrace (c • f) = c * thetaTailTrace f :=
  ((rightJet_tendsto f hf).const_mul c).limUnder_eq

/-- The same source-fixed expression acts on every parameter and every multiplicity. -/
def thetaSpatialAction (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  I * (deriv f x + sourceLogDerivative x * (f x - thetaTailTrace f))

private theorem spatialAction_add (f g : ℝ → ℂ)
    (hf : f ∈ thetaRightJetSpace) (hg : g ∈ thetaRightJetSpace) :
    thetaSpatialAction (f+g) = thetaSpatialAction f + thetaSpatialAction g := by
  funext x
  simp only [thetaSpatialAction, tailTrace_add f g hf hg, Pi.add_apply,
    deriv_add ((rightJet_regular f hf).1 x) ((rightJet_regular g hg).1 x)]
  ring

private theorem spatialAction_smul (c : ℂ) (f : ℝ → ℂ) (hf : f ∈ thetaRightJetSpace) :
    thetaSpatialAction (c • f) = c • thetaSpatialAction f := by
  funext x
  have hd := (((rightJet_regular f hf).1 x).hasDerivAt.const_mul c).deriv
  change deriv (c • f) x = c * deriv f x at hd
  simp only [thetaSpatialAction, tailTrace_smul c f hf, Pi.smul_apply, smul_eq_mul]
  rw [hd]
  ring

private theorem spatialAction_zero : thetaSpatialAction 0 = 0 := by
  have ht : thetaTailTrace 0 = 0 :=
    (tendsto_const_nhds : Tendsto (0 : ℝ → ℂ) atTop (𝓝 0)).limUnder_eq
  ext x
  simp [thetaSpatialAction, ht]

theorem thetaSpatialAction_flatParameterJet_zero (z : ℂ) :
    thetaSpatialAction (flatParameterJet 0 z) = z • flatParameterJet 0 z := by
  funext x
  have he := flatQuotient_source_equation z x
  simp only [thetaSpatialAction, thetaTailTrace_flatParameterJet]
  change I * (deriv (flatQuotient z) x +
    sourceLogDerivative x * (flatQuotient z x - (-1))) = z * flatQuotient z x
  rw [sub_neg_eq_add]
  have h : deriv (flatQuotient z) x + sourceLogDerivative x*(flatQuotient z x+1) =
      -I*(z*flatQuotient z x) := by linear_combination he
  rw [h, ← mul_assoc]
  simp

theorem thetaSpatialAction_flatParameterJet_succ (n : ℕ) (z : ℂ) :
    thetaSpatialAction (flatParameterJet (n+1) z) =
      z • flatParameterJet (n+1) z + ((n:ℂ)+1) • flatParameterJet n z := by
  funext x
  have he := flatParameterJet_succ_source_equation n z x
  simp only [thetaSpatialAction, thetaTailTrace_flatParameterJet, parameterEndpointTrace,
    Nat.succ_ne_zero, if_false, sub_zero, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have h : deriv (flatParameterJet (n+1) z) x +
      sourceLogDerivative x*flatParameterJet (n+1) z x =
      -I*(z*flatParameterJet (n+1) z x+((n:ℂ)+1)*flatParameterJet n z x) := by
    linear_combination he
  rw [h, ← mul_assoc]
  simp

private theorem spatialAction_mem (f : ℝ → ℂ) (hf : f ∈ thetaRightJetSpace) :
    thetaSpatialAction f ∈ thetaRightJetSpace := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨⟨z, n⟩, rfl⟩ := hf
      cases n with
      | zero =>
          rw [thetaSpatialAction_flatParameterJet_zero]
          exact thetaRightJetSpace.smul_mem _ (flatParameterJet_mem_thetaRightJetSpace _ _)
      | succ n =>
          rw [thetaSpatialAction_flatParameterJet_succ]
          exact thetaRightJetSpace.add_mem
            (thetaRightJetSpace.smul_mem _ (flatParameterJet_mem_thetaRightJetSpace _ _))
            (thetaRightJetSpace.smul_mem _ (flatParameterJet_mem_thetaRightJetSpace _ _))
  | zero => rw [spatialAction_zero]; exact thetaRightJetSpace.zero_mem
  | add f g hf hg hAf hAg =>
      rw [spatialAction_add f g hf hg]
      exact thetaRightJetSpace.add_mem hAf hAg
  | smul c f hf hAf =>
      rw [spatialAction_smul c f hf]
      exact thetaRightJetSpace.smul_mem c hAf

/-- An actual differential endomorphism, with no source-domain admission premise. -/
def thetaSpatialGenerator : Module.End ℂ thetaRightJetSpace where
  toFun f := ⟨thetaSpatialAction f, spatialAction_mem f f.property⟩
  map_add' f g := Subtype.ext (spatialAction_add f g f.property g.property)
  map_smul' c f := Subtype.ext (spatialAction_smul c f f.property)

def thetaRightJet (z : ℂ) (n : ℕ) : thetaRightJetSpace :=
  ⟨flatParameterJet n z, flatParameterJet_mem_thetaRightJetSpace n z⟩

def thetaRightHasseJet (z : ℂ) (n : ℕ) : thetaRightJetSpace :=
  (n.factorial : ℂ)⁻¹ • thetaRightJet z n

theorem thetaSpatialGenerator_jet_zero (z : ℂ) :
    thetaSpatialGenerator (thetaRightJet z 0) = z • thetaRightJet z 0 :=
  Subtype.ext (thetaSpatialAction_flatParameterJet_zero z)

theorem thetaSpatialGenerator_jet_succ (z : ℂ) (n : ℕ) :
    thetaSpatialGenerator (thetaRightJet z (n+1)) =
      z • thetaRightJet z (n+1) + ((n:ℂ)+1) • thetaRightJet z n :=
  Subtype.ext (thetaSpatialAction_flatParameterJet_succ n z)

theorem thetaSpatialGenerator_hasse_zero (z : ℂ) :
    thetaSpatialGenerator (thetaRightHasseJet z 0) = z • thetaRightHasseJet z 0 := by
  simpa [thetaRightHasseJet] using thetaSpatialGenerator_jet_zero z

theorem thetaSpatialGenerator_hasse_succ (z : ℂ) (n : ℕ) :
    thetaSpatialGenerator (thetaRightHasseJet z (n+1)) =
      z • thetaRightHasseJet z (n+1) + thetaRightHasseJet z n := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hs : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hc : (((n+1).factorial : ℂ)⁻¹) * ((n:ℂ)+1) = (n.factorial : ℂ)⁻¹ := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  simp only [thetaRightHasseJet, map_smul, thetaSpatialGenerator_jet_succ, smul_add,
    smul_smul, hc]
  congr 1
  rw [mul_comm]

theorem thetaRightHasseJet_zero_ne_zero (z : ℂ) : thetaRightHasseJet z 0 ≠ 0 := by
  intro hz
  have hf : flatParameterJet 0 z = 0 := by
    simpa [thetaRightHasseJet, thetaRightJet] using congrArg Subtype.val hz
  have ht := tendsto_flatParameterJet_atTop 0 z
  rw [hf] at ht
  have hn := tendsto_nhds_unique ht
    (tendsto_const_nhds : Tendsto (0 : ℝ → ℂ) atTop (𝓝 0))
  change (-1 : ℂ) = 0 at hn
  exact (neg_ne_zero.mpr one_ne_zero) hn

end RHTower.PaperThetaEndpoint
