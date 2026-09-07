import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMForcingRegularity

/-!
Height-weighted compact tests recover the original completed gradients from scalar localizations. The full cutoff commutator then bootstraps the actual forced response and both original gradients to every local integer Sobolev order.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane TemperedDistribution
open scoped ContDiff ENNReal SchwartzMap LineDeriv Laplacian
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse GaloisForLFunctions.HTGeometry
noncomputable section

/-- Height times a compact interior test is another actual compact interior test. -/
def InteriorTest.mulHeight (g : InteriorTest) : InteriorTest :=
  g.mulSmooth (fun z : ℂ => (z.im : ℂ)) (Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff)

private theorem mulHeight_divHeight_field (g : InteriorTest) (z : ℂ) :
    (g.mulHeight.divHeight 1).field z = g.field z := by
  change (g.field z*(z.im:ℂ))/(z.im:ℂ)^1 = g.field z
  by_cases hz : (z.im:ℂ) = 0
  · have hg : g.field z = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      obtain ⟨w,hw,he⟩ := g.support hs
      have hy : (z.im:ℂ) ≠ 0 := by rw [← he]; exact Complex.ofReal_ne_zero.mpr w.im_ne_zero
      exact hy hz
    simp [hg]
  · simp [hz]

/-- The original completed gradient can be recovered from differentiated scalar
localizations, with the required cutoff derivative retained. -/
theorem localized_gradient_eq (g : InteriorTest) (i : Fin 2) (h : energyDomain) :
    g.localDistribution ((h : EnergySpace) i.succ) =
      ∂_{direction i} (g.mulHeight.localDistribution (embedding h)) -
        (g.mulHeight.derivative (direction i)).localDistribution (embedding h) := by
  have he := localDistribution_derivative g.mulHeight i h
  have hc : (g.mulHeight.divHeight 1).localDistribution ((h : EnergySpace) i.succ) =
      g.localDistribution ((h : EnergySpace) i.succ) := by
    ext ψ
    rw [InteriorTest.localDistribution_apply,InteriorTest.localDistribution_apply]
    apply integral_congr_ae
    filter_upwards with z
    simp only [InteriorTest.localValue,mulHeight_divHeight_field]
  rw [hc] at he
  rw [he]
  module

/-- Sobolev regularity for all scalar localizations supplies one lower order for
all original completed-gradient localizations, without a multiplier hypothesis. -/
theorem localized_gradient_sobolev {s : ℝ} (h : energyDomain)
    (hh : ∀ g : InteriorTest, MemSobolev s 2 (g.localDistribution (embedding h)))
    (g : InteriorTest) (i : Fin 2) :
    MemSobolev (s-1) 2 (g.localDistribution ((h : EnergySpace) i.succ)) := by
  rw [localized_gradient_eq]
  exact (hh g.mulHeight).lineDerivOp.sub
    ((hh (g.mulHeight.derivative (direction i))).mono (by linarith))

private theorem sum_sobolev {s : ℝ} {f : Fin 2 → 𝓢'(ℂ,ℂ)}
    (hf : ∀ i, MemSobolev s 2 (f i)) : MemSobolev s 2 (∑ i, f i) := by
  simpa only [Fin.sum_univ_two] using (hf 0).add (hf 1)

/-- The complete cutoff identity raises the regularity of every actual scalar
localization by one order. All forcing regularity is discharged from the literal source. -/
theorem full_response_sobolev_step (q : XiZeroCopy) (minusBranch : Bool) (s : ℝ)
    (hh : ∀ g : InteriorTest, MemSobolev s 2
      (g.localDistribution (embedding (weakResponse q minusBranch)))) :
    ∀ g : InteriorTest, MemSobolev (s+1) 2
      (g.localDistribution (embedding (weakResponse q minusBranch))) := by
  intro g
  have hscalar (a : InteriorTest) := (hh a).mono (show s-1 ≤ s by linarith)
  have hgrad (a : InteriorTest) (i : Fin 2) :=
    localized_gradient_sobolev (weakResponse q minusBranch) hh a i
  have hl : MemSobolev (s-1) 2
      (Δ (g.localDistribution (embedding (weakResponse q minusBranch)))) := by
    rw [full_response_local_laplacian]
    exact (((sum_sobolev (fun _ => hscalar _)).add
      ((sum_sobolev (fun i => hgrad _ i)).smul (2:ℂ))).add
      ((hscalar _).smul (parameter q minusBranch))).add
      (full_forcing_local_sobolev q minusBranch _ (s-1))
  have hout := planar_sobolev_gain_two (hscalar g) hl
  convert hout using 1; ring

/-- Every compact interior localization of the constructed full-forcing response
has every nonnegative integer Sobolev order. -/
theorem full_response_local_all_orders (q : XiZeroCopy) (minusBranch : Bool) (n : ℕ)
    (g : InteriorTest) :
    MemSobolev (n:ℝ) 2 (g.localDistribution (embedding (weakResponse q minusBranch))) := by
  have h : ∀ n : ℕ, ∀ g : InteriorTest, MemSobolev ((n:ℝ)+2) 2
      (g.localDistribution (embedding (weakResponse q minusBranch))) := by
    intro n
    induction n with
    | zero => intro g; simpa using full_response_local_H2 q minusBranch g
    | succ n ih =>
      intro g
      have hs := full_response_sobolev_step q minusBranch ((n:ℝ)+2) ih g
      convert hs using 1; push_cast; ring
  exact (h n g).mono (by linarith)

/-- Both original completed gradients of the full response have every localized
integer Sobolev order as well. -/
theorem full_response_gradient_all_orders (q : XiZeroCopy) (minusBranch : Bool) (n : ℕ)
    (g : InteriorTest) (i : Fin 2) :
    MemSobolev (n:ℝ) 2 (g.localDistribution ((weakResponse q minusBranch : EnergySpace) i.succ)) := by
  have h := localized_gradient_sobolev (weakResponse q minusBranch)
    (full_response_local_all_orders q minusBranch (n+1)) g i
  simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using h

end
end RHTower.D4BMModularCore
