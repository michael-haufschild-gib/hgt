import GaloisForLFunctions.RHTower.SuzukiProjectiveDefectBoundary

/-!
# Suzuki's Donoghue spectral-measure connectors

For Suzuki's characteristic pair `A,E`, the canonical Herglotz carrier is not merely an abstract
Cayley transform.  Away from the even-extension divisor it is the quotient of the two
parity-selected characteristic functions

`m(z) = -i W_1(z) / W_{-1}(z)`.

On paper, Suzuki's normalized Livšic formula and the classical Donoghue theorem identify this
function with the resolvent transform of the normalized positive deficiency vector for the
`u=-1` self-adjoint extension.  Its spectral probability `ν` and Nevanlinna measure `μ` obey

`dμ(t) = (1+t²) dν(t)`.

The concrete unbounded source operator and its spectral projections are not yet represented in
Lean, so this module formalizes only the dependency-closed analytic interface of that theorem:

* the exact two-angle quotient;
* its oddness under Suzuki parity;
* the Donoghue kernel decomposition with no linear term;
* the exact pole residue, and its reciprocal boundary-phase-speed form.

No RH assumption and no numerical computation occur here.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **Canonical two-angle Donoghue quotient.**  Suzuki's Herglotz carrier is the quotient of the
odd `u=1` and even `u=-1` extension functions, with the exact factor `-i`. -/
theorem suzukiHerglotz_eq_twoAngleDonoghueQuotient
    {A E : ℂ → ℂ} {z : ℂ}
    (hE : E z ≠ 0)
    (hW : suzukiCharacteristicPencil A E (-1) z ≠ 0) :
    suzukiHerglotz A E z =
      -I * (suzukiCharacteristicPencil A E 1 z /
        suzukiCharacteristicPencil A E (-1) z) := by
  have hAE : A z - E z ≠ 0 := by
    rw [sub_eq_add_neg]
    simpa [suzukiCharacteristicPencil] using hW
  have hEA : E z - A z ≠ 0 := by
    intro h
    apply hAE
    linear_combination -h
  rw [suzukiHerglotz, suzukiUpperCayleyInv, suzukiLivsicQuotient]
  calc
    I * ((1 + A z / E z) / (1 - A z / E z)) =
        I * ((E z + A z) / (E z - A z)) := by
      field_simp [hE, hEA]
    _ = -I * ((A z + E z) / (A z - E z)) := by
      field_simp [hAE, hEA]
      ring
    _ = -I * (suzukiCharacteristicPencil A E 1 z /
        suzukiCharacteristicPencil A E (-1) z) := by
      simp only [suzukiCharacteristicPencil, one_mul, neg_one_mul]
      congr 2

/-- **Odd Donoghue carrier.**  Source parity makes the normalized Herglotz quotient odd wherever
both meromorphic values are finite.  Its Nevanlinna measure is consequently even. -/
theorem suzukiHerglotz_neg_of_parity
    {A E : ℂ → ℂ} (hpar : SuzukiParityPair A E) {z : ℂ}
    (hEz : E z ≠ 0) (hEneg : E (-z) ≠ 0)
    (hW : suzukiCharacteristicPencil A E (-1) z ≠ 0) :
    suzukiHerglotz A E (-z) = -suzukiHerglotz A E z := by
  have hWneg : suzukiCharacteristicPencil A E (-1) (-z) ≠ 0 := by
    rw [suzukiCharacteristicPencil_neg_one_even hpar z]
    exact hW
  rw [suzukiHerglotz_eq_twoAngleDonoghueQuotient hEneg hWneg,
    suzukiHerglotz_eq_twoAngleDonoghueQuotient hEz hW,
    suzukiCharacteristicPencil_one_odd hpar z,
    suzukiCharacteristicPencil_neg_one_even hpar z]
  ring

/-- Scalar kernel in the Donoghue resolvent transform of a spectral probability measure. -/
def suzukiDonoghueKernel (t : ℝ) (z : ℂ) : ℂ :=
  z + (z ^ (2 : ℕ) + 1) / ((t : ℂ) - z)

/-- The resolvent form of the Donoghue kernel is a real-line Möbius kernel. -/
theorem suzukiDonoghueKernel_eq_mobius {t : ℝ} {z : ℂ} (h : (t : ℂ) - z ≠ 0) :
    suzukiDonoghueKernel t z = ((t : ℂ) * z + 1) / ((t : ℂ) - z) := by
  rw [suzukiDonoghueKernel]
  field_simp
  ring

/-- **Zero-linear-mass decomposition.**  Donoghue's kernel is exactly the normalized Nevanlinna
kernel with measure weight multiplied by `1+t²`; no linear term at infinity occurs. -/
theorem suzukiDonoghueKernel_eq_nevanlinna
    {t : ℝ} {z : ℂ} (h : (t : ℂ) - z ≠ 0) :
    suzukiDonoghueKernel t z =
      (((1 + t ^ (2 : ℕ) : ℝ) : ℂ) / ((t : ℂ) - z)) - (t : ℂ) := by
  rw [suzukiDonoghueKernel]
  push_cast
  field_simp
  ring

/-- **Clark atom from angular derivative.**  If an analytic Schur carrier reaches the boundary
value `1` simply with derivative `d`, its Cayley inverse has residue `-2i/d`. -/
theorem suzukiUpperCayleyInv_residue_at_one
    {θ : ℂ → ℂ} {x d : ℂ}
    (hθ : HasDerivAt θ d x) (hone : θ x = 1) (hd : d ≠ 0) :
    Tendsto (fun z : ℂ => (z - x) * suzukiUpperCayleyInv (θ z))
      (𝓝[≠] x) (𝓝 (-2 * I / d)) := by
  have hslope : Tendsto (slope θ x) (𝓝[≠] x) (𝓝 d) :=
    hθ.tendsto_slope
  have hinv : Tendsto (fun z => (slope θ x z)⁻¹) (𝓝[≠] x) (𝓝 d⁻¹) :=
    hslope.inv₀ hd
  have hθlim : Tendsto θ (𝓝[≠] x) (𝓝 1) := by
    have hcont := hθ.continuousAt.tendsto
    rw [hone] at hcont
    change Tendsto θ (𝓝 x ⊓ 𝓟 {x}ᶜ) (𝓝 1)
    exact hcont.mono_left inf_le_left
  have honeadd : Tendsto (fun z : ℂ => (1 : ℂ) + θ z)
      (𝓝[≠] x) (𝓝 ((1 : ℂ) + 1)) := tendsto_const_nhds.add hθlim
  have hnegI : Tendsto (fun _ : ℂ => (-I : ℂ)) (𝓝[≠] x) (𝓝 (-I)) :=
    tendsto_const_nhds
  have hmain := (hnegI.mul honeadd).mul hinv
  have hmain' : Tendsto
      (fun z : ℂ => -I * (1 + θ z) * (slope θ x z)⁻¹)
      (𝓝[≠] x) (𝓝 (-I * (1 + 1) * d⁻¹)) := hmain
  have hlimit : -I * ((1 : ℂ) + 1) * d⁻¹ = -2 * I / d := by
    field_simp [hd]
    ring_nf
  rw [hlimit] at hmain'
  refine hmain'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [mem_compl_iff, mem_singleton_iff] at hz
  rw [suzukiUpperCayleyInv, slope_def_field, hone]
  have hzx : z - x ≠ 0 := sub_ne_zero.mpr hz
  by_cases hden : 1 - θ z = 0
  · have htheq : θ z = 1 := (sub_eq_zero.mp hden).symm
    simp [htheq]
  · have hthetaNe : θ z ≠ 1 := by
      intro h
      apply hden
      rw [h]
      ring
    have hden' : θ z - 1 ≠ 0 := sub_ne_zero.mpr hthetaNe
    field_simp [hzx, hden, hden']
    ring

/-- **Reciprocal phase-speed law.**  At a boundary point with positive angular speed `q`, the
Nevanlinna atom has weight `2/q`, equivalently the Herglotz residue is `-2/q`. -/
theorem suzukiUpperCayleyInv_phase_residue_at_one
    {θ : ℂ → ℂ} {x : ℂ} {phaseSpeed : ℝ}
    (hθ : HasDerivAt θ (I * (phaseSpeed : ℂ)) x)
    (hone : θ x = 1) (hspeed : 0 < phaseSpeed) :
    Tendsto (fun z : ℂ => (z - x) * suzukiUpperCayleyInv (θ z))
      (𝓝[≠] x) (𝓝 (-((2 / phaseSpeed : ℝ) : ℂ))) := by
  have hd : I * (phaseSpeed : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (ofReal_ne_zero.mpr hspeed.ne')
  have h := suzukiUpperCayleyInv_residue_at_one hθ hone hd
  have hcast : (((2 / phaseSpeed : ℝ) : ℂ)) =
      (2 : ℂ) / (phaseSpeed : ℂ) := by norm_cast
  have hvalue : -2 * I / (I * (phaseSpeed : ℂ)) =
      -((2 / phaseSpeed : ℝ) : ℂ) := by
    rw [hcast]
    field_simp [hspeed.ne']
  rw [hvalue] at h
  exact h

end GaloisForLFunctions.RHTower
