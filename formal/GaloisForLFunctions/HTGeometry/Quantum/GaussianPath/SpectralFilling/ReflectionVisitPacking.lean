import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PrefixPhaseHorizon
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.TimedReflection

/-! # How many distinct spectral reflections can a bounded-time orbit visit? -/
open Matrix Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Each distinct reflection costs at least (1−2ε) of operator path length
between visits, even when the visiting phase can vary with the reflection. -/
theorem spectral_reflection_visit_count {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) (H : selfAdjoint (Reg n))
    (S : Finset (Fin d → Bool)) (a T ε : ℝ) (hε : 2*ε < 1)
    (hhit : ∀ x ∈ S, ∃ t ∈ Icc a (a+T), ∃ z : ℂ, ‖z‖ = 1 ∧
      ‖unitaryEvolution H.val t - z • anchoredSpectralBooleanReflection e V x‖ ≤ ε) :
    S.card ≤ ⌊‖H.val‖*T/(1-2*ε)⌋₊+1 := by
  classical
  let R := anchoredSpectralBooleanReflection e V
  let L := ‖H.val‖
  let s := 1-2*ε
  have hs : 0 < s := sub_pos.mpr hε
  have hL : 0 ≤ L := norm_nonneg _
  choose t ht z hz hnear using fun x : ↥S => hhit x x.property
  let f (x : ↥S) := L*(t x-a)/s
  have hnon (x) : 0 ≤ f x := div_nonneg (mul_nonneg hL (sub_nonneg.mpr (ht x).1)) hs.le
  have hhi (x) : f x ≤ L*T/s := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith only [(ht x).2]) hL) hs.le
  let box (x : ↥S) : Fin (⌊L*T/s⌋₊+1) := ⟨⌊f x⌋₊,Nat.lt_succ_of_le (Nat.floor_mono (hhi x))⟩
  have hinj : Function.Injective box := by
    intro x y he
    by_contra hxy
    have hfloor : ⌊f x⌋₊ = ⌊f y⌋₊ := congrArg Fin.val he
    have hunit : |f x-f y| < 1 := by
      have hx := Nat.lt_floor_add_one (f x)
      have hy := Nat.lt_floor_add_one (f y)
      have hlo := Nat.floor_le (hnon x)
      have hlo' := Nat.floor_le (hnon y)
      rw [hfloor] at hx hlo
      exact abs_lt.mpr ⟨by linarith only [hy,hlo],by linarith only [hx,hlo']⟩
    have hscale : |f x-f y| = L*|t x-t y|/s := by
      rw [show f x-f y = L*(t x-t y)/s by dsimp [f]; ring,abs_div,abs_mul,abs_of_nonneg hL,abs_of_pos hs]
    rw [hscale] at hunit
    have hstep := (norm_unitaryEvolution_time_sub_le H.2 (t x) (t y)).trans_lt (by simpa only [one_mul] using (div_lt_iff₀ hs).mp hunit)
    let w := (z x)⁻¹*z y
    have hw : ‖w‖ = 1 := by dsimp [w]; rw [norm_mul,norm_inv,hz,hz,inv_one,one_mul]
    have hrotate : z x • (R x-w • R y) = z x • R x-z y • R y := by
      rw [smul_sub,smul_smul,show z x*w = z y by dsimp [w]; rw [← mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)),one_mul]]
    have hsep : 1 ≤ ‖z x • R x-z y • R y‖ := by
      rw [← hrotate,norm_smul,hz,one_mul]
      exact anchoredSpectralBooleanReflection_projective_separated e V (fun h => hxy (Subtype.ext h)) w hw
    have hx : ‖z x • R x-unitaryEvolution H.val (t x)‖ ≤ ε := (norm_sub_rev _ _).le.trans (hnear x)
    have hy : ‖unitaryEvolution H.val (t y)-z y • R y‖ ≤ ε := hnear y
    have h1 := norm_sub_le_norm_sub_add_norm_sub (z x • R x) (unitaryEvolution H.val (t x)) (z y • R y)
    have h2 := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution H.val (t x)) (unitaryEvolution H.val (t y)) (z y • R y)
    change ‖unitaryEvolution H.val (t x)-unitaryEvolution H.val (t y)‖ < 1-2*ε at hstep
    linarith only [h1,h2,hx,hy,hstep,hsep]
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective box hinj

/-- Any full relative-phase filling interval at fixed error must already
traverse a doubly exponential number of distinguishable sign targets. -/
theorem phase_filling_requires_spectral_length {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n)) (a T : ℝ) (hT : 0 ≤ T)
    (hphase : ∀ c : Fin d → ℝ, ∃ t ∈ Icc a (a+T), ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-c j) < 1/80) :
    ((2:ℝ)^d-1)*(39/40) ≤ ‖H.val‖*T := by
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  have hc := spectral_reflection_visit_count e V H Finset.univ a T (1/80) (by norm_num)
    (fun x _ => phase_interval_approaches_reflection e H a (a+T) hphase x)
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hc
  have hh : (2:ℝ)^d ≤ (⌊‖H.val‖*T/(1-2*(1/80:ℝ))⌋₊:ℝ)+1 := by exact_mod_cast hc
  have hf := Nat.floor_le (show 0 ≤ ‖H.val‖*T/(1-2*(1/80:ℝ)) from div_nonneg (mul_nonneg (norm_nonneg _) hT) (by norm_num))
  rw [show (1-2*(1/80:ℝ)) = 39/40 by norm_num] at hh hf
  exact (le_div_iff₀ (by norm_num : (0:ℝ)<39/40)).mp ((sub_le_iff_le_add.mpr hh).trans hf)

/-- Almost surely, filling all phases on a sufficiently long Gaussian Pauli
prefix costs at least a fixed multiple of (2^(2^N−1)−1)/N in physical time. -/
theorem gaussian_pauli_phase_cover_time_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in Filter.atTop,
      let N := k+3
      let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a T : ℝ, 0 ≤ T → (∀ c : Fin (2^N-1) → ℝ, ∃ t ∈ Icc a (a+T), ∀ j,
        turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-c j) < 1/80) →
          ((2:ℝ)^(2^N-1)-1)*(39/40) ≤ C*(N:ℝ)*T := by
  obtain ⟨_,b,_,hb,hw⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨12+b,by positivity,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hω] with k hmass
  intro N e H a T hT hfill
  let u := pathPauliDisorderShell ω (k+1)
  have hn : ‖pathHamiltonian u‖ ≤ ∑ l, |u l| := by
    rw [pathHamiltonian_eq_sum]
    exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun l _ => by
      rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one])
  exact (phase_filling_requires_spectral_length e H a T hT hfill).trans
    (mul_le_mul_of_nonneg_right (hn.trans (path_pauli_coefficient_mass_le u b hmass.2)) hT)

#print axioms gaussian_pauli_phase_cover_time_lower
#print axioms spectral_reflection_visit_count
#print axioms phase_filling_requires_spectral_length
end
end GaloisForLFunctions.HTGeometry
