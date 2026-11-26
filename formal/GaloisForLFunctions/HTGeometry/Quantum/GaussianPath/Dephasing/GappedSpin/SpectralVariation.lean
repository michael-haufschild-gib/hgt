import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.OddInverse
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.NearbySpectrum

/-! # Quadratic spectral variation across separated spin sectors -/

namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin
noncomputable section
variable {A : Type*} [CStarAlgebra A]

private theorem inverse_norm {X : A} (u : Aˣ) (hu : (u:A)=1-X) {b : ℝ}
    (hx : ‖X‖≤b) (hb : b<1) : ‖(↑u⁻¹:A)‖≤1/(1-b) := by
  let Y : A := ↑u⁻¹
  have he : Y*(1-X)=1 := by rw [←hu]; exact u.inv_mul
  rw [mul_sub,mul_one,sub_eq_iff_eq_add] at he
  have hone : ‖(1:A)‖≤1 := by
    rcases subsingleton_or_nontrivial A with hs | hn
    · rw [@Subsingleton.elim A hs 1 0,norm_zero]
      exact zero_le_one
    · letI := hn
      exact (norm_one (α:=A)).le
  have h : ‖Y‖≤1+‖Y‖*b := calc
    _ = ‖1+Y*X‖ := congrArg norm he
    _ ≤ ‖(1:A)‖+‖Y*X‖ := norm_add_le ..
    _ ≤ _ := add_le_add hone ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _)))
  apply (le_div_iff₀ (sub_pos.mpr hb)).mpr
  linarith only [h]

/-- An invertible approximate intertwiner controls both inclusions of
normal spectra. The conjugated operators need not be normal. -/
private theorem near_intertwined (H L : A) [IsStarNormal H] [IsStarNormal L] (u : Aˣ)
    {r : ℝ} (hr : ‖(↑u⁻¹:A)‖*‖H*(u:A)-(u:A)*L‖<r) :
    (∀ z∈spectrum ℂ H, ∃ w∈spectrum ℂ L, ‖z-w‖<r) ∧
      (∀ w∈spectrum ℂ L, ∃ z∈spectrum ℂ H, ‖w-z‖<r) := by
  let Y : A := ↑u⁻¹
  let D := H*(u:A)-(u:A)*L
  have hleft : Y*H*(u:A)-L=Y*D := by
    dsimp only [D]; rw [mul_sub,←mul_assoc Y H,←mul_assoc Y (u:A),show Y*(u:A)=1 from u.inv_mul,one_mul]
  have hright : (u:A)*L*Y-H=-(D*Y) := by
    dsimp only [D]; rw [sub_mul,mul_assoc H,show (u:A)*Y=1 from u.mul_inv,mul_one,neg_sub]
  constructor
  · intro z hz
    apply SpectralApproximation.nearby_spectral_point (U:=Y*H*(u:A)) (V:=L) (z:=z) ?_ ?_
    · simpa only [Y,spectrum.units_conjugate'] using hz
    · rw [hleft]; exact (norm_mul_le Y D).trans_lt hr
  · intro z hz
    apply SpectralApproximation.nearby_spectral_point (U:=(u:A)*L*Y) (V:=H) (z:=z) ?_ ?_
    · simpa only [Y,spectrum.units_conjugate] using hz
    · rw [hright,norm_neg]; exact ((norm_mul_le D Y).trans_eq (mul_comm ..)).trans_lt hr

/-- The spectral edges, and indeed both whole spectra, move only
quadratically with a perturbation between separated sectors. -/
theorem transverse_spectrum (Z W V : A) (hz : IsSelfAdjoint Z)
    (hw : IsSelfAdjoint W) (hv : IsSelfAdjoint V) (hZ : Z*Z=1) (hn : ‖Z‖≤1)
    (hW : Z*W=W*Z) (hV : Z*V=-(V*Z)) {h : ℝ} (hg : ‖W‖<h) :
    let L := h • Z+W
    let b := ‖V‖/(2*(h-‖W‖))
    ∀ r : ℝ, b<1 → ‖V‖*b/(1-b)<r →
      (∀ z∈spectrum ℂ (L+V), ∃ w∈spectrum ℂ L, ‖z-w‖<r) ∧
      (∀ w∈spectrum ℂ L, ∃ z∈spectrum ℂ (L+V), ‖w-z‖<r) := by
  intro L b r hb hr
  obtain ⟨X,hX,hbX⟩ := odd_commutator_inverse Z W V hZ hn hW hV hg
  have hi := isUnit_one_sub_of_norm_lt_one (hbX.trans_lt hb)
  let u := hi.unit
  have hu : (u:A)=1-X := hi.unit_spec
  have hL : IsSelfAdjoint L := by
    change star (h • Z+W)=h • Z+W
    rw [star_add,star_smul,hz.star_eq,hw.star_eq,star_trivial]
  letI : IsStarNormal L := hL.isStarNormal
  letI : IsStarNormal (L+V) := (hL.add hv).isStarNormal
  apply near_intertwined (L+V) L u
  have hd : (L+V)*(u:A)-(u:A)*L=-(V*X) := calc
    _ = V-(L*X-X*L)-V*X := by rw [hu]; noncomm_ring
    _ = _ := by rw [show L*X-X*L=V from hX,sub_self,zero_sub]
  rw [hd,norm_neg]
  exact (mul_le_mul (inverse_norm u hu hbX hb) ((norm_mul_le ..).trans
    (mul_le_mul_of_nonneg_left hbX (norm_nonneg _))) (norm_nonneg _) (by positivity)).trans_lt
    ((show 1/(1-b)*(‖V‖*b)=‖V‖*b/(1-b) by ring).trans_lt hr)

#print axioms transverse_spectrum
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin
