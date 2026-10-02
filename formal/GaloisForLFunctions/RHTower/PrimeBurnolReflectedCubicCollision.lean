import GaloisForLFunctions.RHTower.PrimeBurnolThetaModularHolonomy

/-!
# Coherent reflected Burnol cubic: collision poles and finite part

The complete two-column Gram of one literal Burnol prime-depth cell retains the cross term
between opposite clocks. Unlike an orthogonal theta doubling, this Gram moves the neutral
reference. Its density-weighted cubic has a second-order real pole and a first-order imaginary
pole as the clocks collide. Every nonzero actual theta twist has imaginary trace tending to
positive infinity from the positive clock chamber, so raw reflection does not inherit a
uniform source budget.

The exact positive survivor is a canonical subtraction of both principal poles. The remaining
real trace tends to `14*d*v*(2*u-1)/3`; the remaining imaginary trace tends to zero. Here d is
literal column mass, u is squared theta visibility, and v is visibility times contrast.
All inverse claims exclude zero clock separation; finite-part limits use punctured neighborhoods.

This is a source-native obstruction and local renormalization law. It neither identifies the
required four-leg completion with this two-column block nor supplies mixed-prime control,
a Gamma counterterm identity, a Hardy index comparison, or an RH conclusion.
-/

open Matrix
open Filter Set Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

private def coherentGram (z w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,z;w,1]
private def gramInv (z w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1-z*w)⁻¹ • !![1,-z;-w,1]
private def proj (u v : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![u,v;v,1-u]
private def corner : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,0]

private theorem coherent_inverse (z w : ℂ) (h : 1-z*w ≠ 0) :
    gramInv z w * coherentGram z w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramInv, coherentGram, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

private theorem traceless_cube (A : Matrix (Fin 2) (Fin 2) ℂ) (h : A.trace = 0) :
    A^3 = (A 0 0 ^2 + A 0 1*A 1 0) • A := by
  have h11 : A 1 1 = -A 0 0 := by
    have h' : A 0 0 + A 1 1 = 0 := by simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using h
    linear_combination h'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h11] <;> ring_nf <;> simp

private theorem reflected_trace (z w u v : ℂ) (h : 1-z*w ≠ 0) :
    Matrix.trace (coherentGram z w * cubicProjectionAssociatorAlgebra
      (gramInv z w * proj u v * coherentGram z w) (proj u v) corner) =
      v*(z+w)*(z*w*(1-2*u)+v*(z-w))/(1-z*w) := by
  let r := gramInv z w * proj u v * coherentGram z w
  have hr : r.trace = 1 := by
    simp [r, gramInv, proj, coherentGram, Matrix.trace, Matrix.diag,
      Fin.sum_univ_two]
    field_simp
    ring
  have hp : corner.trace = 1 := by simp [corner, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have hq : (proj u v).trace = 1 := by simp [proj, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  change Matrix.trace (coherentGram z w * cubicProjectionAssociatorAlgebra r (proj u v) corner) = _
  rw [cubicProjectionAssociatorAlgebra,
    traceless_cube (r-corner) (by rw [Matrix.trace_sub, hr, hp, sub_self]),
    traceless_cube (r-proj u v) (by rw [Matrix.trace_sub, hr, hq, sub_self]),
    traceless_cube (proj u v-corner) (by rw [Matrix.trace_sub, hq, hp, sub_self])]
  simp [r, coherentGram, gramInv, proj, corner, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.trace, Matrix.diag]
  field_simp
  ring

private def coherence (lam k : ℝ) : ℂ :=
  ((lam : ℂ) / ((lam : ℂ) - Complex.I*(k : ℂ)))^3

private theorem coherence_re (lam k : ℝ) :
    (coherence lam k).re = lam^4*(lam^2-3*k^2)/(lam^2+k^2)^3 := by
  simp only [div_eq_mul_inv]
  simp [coherence, pow_succ, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, Complex.normSq_apply]
  ring

private theorem coherence_im (lam k : ℝ) :
    (coherence lam k).im = lam^3*k*(3*lam^2-k^2)/(lam^2+k^2)^3 := by
  simp only [div_eq_mul_inv]
  simp [coherence, pow_succ, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, Complex.normSq_apply]
  ring

private theorem coherence_normSq (lam k : ℝ) :
    Complex.normSq (coherence lam k) = lam^6/(lam^2+k^2)^3 := by
  have he : Complex.normSq ((lam : ℂ)-Complex.I*(k : ℂ)) = lam^2+k^2 := by
    simp [Complex.normSq_apply]
    ring
  rw [coherence, map_pow, Complex.normSq_div, he, Complex.normSq_ofReal, div_pow]
  congr 1
  ring

private theorem coherence_gap {lam : ℝ} (hlam : 0 < lam) (k : ℝ) :
    1-Complex.normSq (coherence lam k) =
      k^2*(3*lam^4+3*lam^2*k^2+k^4)/(lam^2+k^2)^3 := by
  rw [coherence_normSq]
  have hs : lam^2+k^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

private theorem coherence_gap_ne {lam k : ℝ} (hlam : 0 < lam) (hk : k ≠ 0) :
    1-coherence lam k * star (coherence lam k) ≠ 0 := by
  rw [Complex.star_def, Complex.mul_conj]
  have hg : 0 < 1-Complex.normSq (coherence lam k) := by
    rw [coherence_gap hlam]
    positivity
  exact_mod_cast hg.ne'

private def reflectedResponse (lam u v k : ℝ) : ℂ :=
  let z := coherence lam k
  Matrix.trace (coherentGram z (star z) * cubicProjectionAssociatorAlgebra
    (gramInv z (star z) * proj (u : ℂ) (v : ℂ) * coherentGram z (star z))
    (proj (u : ℂ) (v : ℂ)) corner)

private theorem reflectedResponse_re {lam k : ℝ} (hlam : 0 < lam) (hk : k ≠ 0)
    (u v : ℝ) :
    (reflectedResponse lam u v k).re =
      -2*v*(2*u-1)*lam^10*(lam^2-3*k^2)/
        (k^2*(3*lam^4+3*lam^2*k^2+k^4)*(lam^2+k^2)^3) := by
  rw [reflectedResponse, reflected_trace _ _ _ _ (coherence_gap_ne hlam hk),
    Complex.star_def, Complex.mul_conj]
  have he : (1 : ℂ) - (Complex.normSq (coherence lam k) : ℂ) =
      ((1-Complex.normSq (coherence lam k) : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.div_ofReal_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
    Complex.re_ofNat, Complex.im_ofNat]
  norm_num only
  rw [coherence_gap hlam]
  simp only [coherence_re, coherence_im, coherence_normSq]
  have hs : lam^2+k^2 ≠ 0 := ne_of_gt (by positivity)
  have hH : 3*lam^4+3*lam^2*k^2+k^4 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

private theorem reflectedResponse_im {lam k : ℝ} (hlam : 0 < lam) (hk : k ≠ 0)
    (u v : ℝ) :
    (reflectedResponse lam u v k).im =
      4*v^2*lam^7*(lam^2-3*k^2)*(3*lam^2-k^2)/
        (k*(3*lam^4+3*lam^2*k^2+k^4)*(lam^2+k^2)^3) := by
  rw [reflectedResponse, reflected_trace _ _ _ _ (coherence_gap_ne hlam hk),
    Complex.star_def, Complex.mul_conj]
  have he : (1 : ℂ) - (Complex.normSq (coherence lam k) : ℂ) =
      ((1-Complex.normSq (coherence lam k) : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.div_ofReal_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
    Complex.re_ofNat, Complex.im_ofNat]
  norm_num only
  rw [coherence_gap hlam]
  simp only [coherence_re, coherence_im, coherence_normSq]
  have hs : lam^2+k^2 ≠ 0 := ne_of_gt (by positivity)
  have hH : 3*lam^4+3*lam^2*k^2+k^4 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

private def collisionDenom (lam k : ℝ) : ℝ :=
  (3*lam^4+3*lam^2*k^2+k^4)*(lam^2+k^2)^3

private def regularReal (lam u v k : ℝ) : ℝ :=
  2*v*(2*u-1)*lam^2*(21*lam^8+19*lam^6*k^2+15*lam^4*k^4+6*lam^2*k^6+k^8)/
    (3*collisionDenom lam k)

private def regularImag (lam v k : ℝ) : ℝ :=
  -4*v^2*lam*k*(22*lam^8+16*lam^6*k^2+15*lam^4*k^4+6*lam^2*k^6+k^8)/
    collisionDenom lam k

private theorem real_subtraction {lam k : ℝ} (hlam : 0 < lam) (hk : k ≠ 0)
    (u v : ℝ) :
    (reflectedResponse lam u v k).re + 2*v*(2*u-1)*lam^2/(3*k^2) =
      regularReal lam u v k := by
  rw [reflectedResponse_re hlam hk]
  dsimp [regularReal, collisionDenom]
  have hs : lam^2+k^2 ≠ 0 := ne_of_gt (by positivity)
  have hH : 3*lam^4+3*lam^2*k^2+k^4 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

private theorem imag_subtraction {lam k : ℝ} (hlam : 0 < lam) (hk : k ≠ 0)
    (u v : ℝ) :
    (reflectedResponse lam u v k).im - 4*v^2*lam/k = regularImag lam v k := by
  rw [reflectedResponse_im hlam hk]
  dsimp [regularImag, collisionDenom]
  have hs : lam^2+k^2 ≠ 0 := ne_of_gt (by positivity)
  have hH : 3*lam^4+3*lam^2*k^2+k^4 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

private theorem regularReal_limit {lam : ℝ} (hlam : 0 < lam) (u v : ℝ) :
    Tendsto (fun k => (reflectedResponse lam u v k).re +
      2*v*(2*u-1)*lam^2/(3*k^2)) (𝓝[≠] (0 : ℝ)) (𝓝 (14/3*v*(2*u-1))) := by
  have hc : ContinuousAt (regularReal lam u v) 0 := by
    unfold regularReal collisionDenom
    fun_prop (disch := positivity)
  have he : regularReal lam u v 0 = 14/3*v*(2*u-1) := by
    dsimp [regularReal, collisionDenom]
    field_simp
    ring
  rw [← he]
  apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  exact (real_subtraction hlam (by simpa using hk) u v).symm

private theorem regularImag_limit {lam : ℝ} (hlam : 0 < lam) (u v : ℝ) :
    Tendsto (fun k => (reflectedResponse lam u v k).im - 4*v^2*lam/k)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hc : ContinuousAt (regularImag lam v) 0 := by
    unfold regularImag collisionDenom
    fun_prop (disch := positivity)
  have he : regularImag lam v 0 = 0 := by simp [regularImag]
  have hc' := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
  rw [he] at hc'
  apply hc'.congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  exact (imag_subtraction hlam (by simpa using hk) u v).symm

private theorem imaginary_pole_limit {lam : ℝ} (hlam : 0 < lam) (u v : ℝ) :
    Tendsto (fun k => k*(reflectedResponse lam u v k).im)
      (𝓝[>] (0 : ℝ)) (𝓝 (4*v^2*lam)) := by
  let f := fun k => 4*v^2*lam^7*(lam^2-3*k^2)*(3*lam^2-k^2)/collisionDenom lam k
  have hc : ContinuousAt f 0 := by
    dsimp [f, collisionDenom]
    fun_prop (disch := positivity)
  have he : f 0 = 4*v^2*lam := by
    dsimp [f, collisionDenom]
    field_simp
    ring
  rw [← he]
  apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hk0 : k ≠ 0 := ne_of_gt hk
  rw [reflectedResponse_im hlam hk0]
  dsimp [f, collisionDenom]
  field_simp

private theorem imaginary_pole_atTop {lam : ℝ} (hlam : 0 < lam) (u : ℝ)
    {v : ℝ} (hv : v ≠ 0) :
    Tendsto (fun k => (reflectedResponse lam u v k).im) (𝓝[>] (0 : ℝ)) atTop := by
  have h := (imaginary_pole_limit hlam u v).pos_mul_atTop (by positivity)
    tendsto_inv_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hk0 : k ≠ 0 := ne_of_gt hk
  field_simp

namespace RHTower

/-- The literal diagonal mass of one prime-depth Burnol column. -/
def primeBurnolReflectedPairMass (pe : Nat.Primes × ℕ) : ℝ :=
  (primeBurnolAmplitude pe).re^2 / (4*primeBurnolLogFrequency pe^3)

theorem primeBurnolReflectedPairMass_pos (pe : Nat.Primes × ℕ) :
    0 < primeBurnolReflectedPairMass pe := by
  have hA : (primeBurnolAmplitude pe).re ≠ 0 := by
    simpa only [primeBurnolAmplitude, Complex.ofReal_re, ne_eq, Complex.ofReal_eq_zero]
      using primeBurnolAmplitude_ne_zero pe
  have hl := primeBurnolLogFrequency_pos pe
  unfold primeBurnolReflectedPairMass
  positivity

/-- Full coherence of a Burnol column with its opposite-clock column. -/
def primeBurnolReflectedCoherence (pe : Nat.Primes × ℕ) (k : ℝ) : ℂ :=
  coherence (primeBurnolLogFrequency pe) k

/-- Both reflected columns remain labelled and their cross terms are retained. -/
def primeBurnolReflectedPairGram (pe : Nat.Primes × ℕ) (k : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.gram ℂ ![primeBurnolWindowFeatureLp pe k, primeBurnolWindowFeatureLp pe (-k)]

private theorem reflectedMass_cast (pe : Nat.Primes × ℕ) :
    (primeBurnolReflectedPairMass pe : ℂ) =
      primeBurnolAmplitude pe*primeBurnolAmplitude pe /
        (4*(primeBurnolLogFrequency pe : ℂ)^3) := by
  unfold primeBurnolReflectedPairMass
  push_cast
  rw [show ((primeBurnolAmplitude pe).re : ℂ) = primeBurnolAmplitude pe by
    simp [primeBurnolAmplitude]]
  ring

theorem primeBurnolReflectedPairGram_eq (pe : Nat.Primes × ℕ) (k : ℝ) :
    primeBurnolReflectedPairGram pe k = (primeBurnolReflectedPairMass pe : ℂ) •
      !![1, primeBurnolReflectedCoherence pe k; star (primeBurnolReflectedCoherence pe k), 1] := by
  have hl : (primeBurnolLogFrequency pe : ℂ) ≠ 0 := by
    exact_mod_cast (primeBurnolLogFrequency_pos pe).ne'
  have hminus : (primeBurnolLogFrequency pe : ℂ)-Complex.I*(k : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact (primeBurnolLogFrequency_pos pe).ne' hr
  have hplus : (primeBurnolLogFrequency pe : ℂ)+Complex.I*(k : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact (primeBurnolLogFrequency_pos pe).ne' hr
  have hsame (x : ℝ) : primeBurnolPairRate pe pe x x =
      2*(primeBurnolLogFrequency pe : ℂ) := by simp [primeBurnolPairRate]; ring
  have hm : primeBurnolPairRate pe pe k (-k) =
      2*((primeBurnolLogFrequency pe : ℂ)-Complex.I*(k : ℂ)) := by
    simp [primeBurnolPairRate]
    ring
  have hp : primeBurnolPairRate pe pe (-k) k =
      2*((primeBurnolLogFrequency pe : ℂ)+Complex.I*(k : ℂ)) := by
    simp [primeBurnolPairRate]
    ring
  ext i j
  fin_cases i <;> fin_cases j
  · change inner ℂ (primeBurnolWindowFeatureLp pe k) (primeBurnolWindowFeatureLp pe k) =
      (primeBurnolReflectedPairMass pe : ℂ)*1
    rw [inner_primeBurnolWindowFeatureLp_eq, hsame, reflectedMass_cast]
    field_simp
    ring
  · change inner ℂ (primeBurnolWindowFeatureLp pe k) (primeBurnolWindowFeatureLp pe (-k)) =
      (primeBurnolReflectedPairMass pe : ℂ)*primeBurnolReflectedCoherence pe k
    rw [inner_primeBurnolWindowFeatureLp_eq, hm, reflectedMass_cast]
    dsimp [primeBurnolReflectedCoherence, coherence]
    field_simp
    ring
  · change inner ℂ (primeBurnolWindowFeatureLp pe (-k)) (primeBurnolWindowFeatureLp pe k) =
      (primeBurnolReflectedPairMass pe : ℂ)*star (primeBurnolReflectedCoherence pe k)
    rw [inner_primeBurnolWindowFeatureLp_eq, hp, reflectedMass_cast]
    simp [primeBurnolReflectedCoherence, coherence]
    field_simp
    ring
  · change inner ℂ (primeBurnolWindowFeatureLp pe (-k)) (primeBurnolWindowFeatureLp pe (-k)) =
      (primeBurnolReflectedPairMass pe : ℂ)*1
    rw [inner_primeBurnolWindowFeatureLp_eq, hsame, reflectedMass_cast]
    field_simp
    ring

/-- The rational inverse formula is used only off the collision in inverse claims. -/
def primeBurnolReflectedPairInverse (pe : Nat.Primes × ℕ) (k : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (primeBurnolReflectedPairMass pe : ℂ)⁻¹ •
    gramInv (primeBurnolReflectedCoherence pe k) (star (primeBurnolReflectedCoherence pe k))

theorem primeBurnolReflectedPairInverse_mul (pe : Nat.Primes × ℕ) (k : ℝˣ) :
    primeBurnolReflectedPairInverse pe k * primeBurnolReflectedPairGram pe k = 1 := by
  have hd : (primeBurnolReflectedPairMass pe : ℂ) ≠ 0 := by
    exact_mod_cast (primeBurnolReflectedPairMass_pos pe).ne'
  rw [primeBurnolReflectedPairGram_eq, primeBurnolReflectedPairInverse]
  change ((primeBurnolReflectedPairMass pe : ℂ)⁻¹ • gramInv _ _) *
    ((primeBurnolReflectedPairMass pe : ℂ) • coherentGram _ _) = _
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hd, one_smul]
  exact coherent_inverse _ _ (coherence_gap_ne (primeBurnolLogFrequency_pos pe) k.ne_zero)

private theorem reflected_theta_projection (pe : Nat.Primes × ℕ) (a : ℝ) :
    primeBurnolThetaBlock a pe.1 * corner * primeBurnolThetaBlock (-a) pe.1 =
      proj ((primeBurnolThetaVisibility a pe.1 : ℂ)^2)
        ((primeBurnolThetaVisibility a pe.1 : ℂ)*(primeBurnolThetaContrast a pe.1 : ℂ)) := by
  have hp : (primeBurnolThetaVisibility a pe.1 : ℂ)^2 +
      (primeBurnolThetaContrast a pe.1 : ℂ)^2 = 1 := by
    exact_mod_cast primeBurnolThetaVisibility_sq_add_contrast_sq a pe.1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primeBurnolThetaBlock, primeBurnolThetaVisibility_neg,
      primeBurnolThetaContrast_neg, corner, proj] <;> ring_nf
  linear_combination hp

/-- Density-weighted cubic of the literal coherent reflected source and actual theta rotation. -/
def primeBurnolReflectedThetaCubicTrace (pe : Nat.Primes × ℕ) (a k : ℝ) : ℂ :=
  let G := primeBurnolReflectedPairGram pe k
  let q := primeBurnolThetaBlock a pe.1 * corner * primeBurnolThetaBlock (-a) pe.1
  Matrix.trace (G * cubicProjectionAssociatorAlgebra
    (primeBurnolReflectedPairInverse pe k * q * G) q corner)

private theorem reflected_trace_normalization (pe : Nat.Primes × ℕ) (a k : ℝ) :
    primeBurnolReflectedThetaCubicTrace pe a k =
      (primeBurnolReflectedPairMass pe : ℂ) * reflectedResponse
        (primeBurnolLogFrequency pe) (primeBurnolThetaVisibility a pe.1^2)
        (primeBurnolThetaVisibility a pe.1*primeBurnolThetaContrast a pe.1) k := by
  have hd : (primeBurnolReflectedPairMass pe : ℂ) ≠ 0 := by
    exact_mod_cast (primeBurnolReflectedPairMass_pos pe).ne'
  simp only [primeBurnolReflectedThetaCubicTrace, primeBurnolReflectedPairGram_eq,
    reflected_theta_projection, primeBurnolReflectedPairInverse,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hd, one_smul,
    Matrix.trace_smul, smul_eq_mul]
  simp only [reflectedResponse, primeBurnolReflectedCoherence,
    coherentGram, Complex.ofReal_pow, Complex.ofReal_mul]

/-- Exact ordinary trace after coherent reflection; no finite charge is inserted by hand. -/
theorem primeBurnolReflectedThetaCubicTrace_eq
    (pe : Nat.Primes × ℕ) (a : ℝ) (k : ℝˣ) :
    let d : ℂ := primeBurnolReflectedPairMass pe
    let z := primeBurnolReflectedCoherence pe k
    let u : ℂ := (primeBurnolThetaVisibility a pe.1 : ℂ)^2
    let v : ℂ := (primeBurnolThetaVisibility a pe.1 : ℂ)*(primeBurnolThetaContrast a pe.1 : ℂ)
    primeBurnolReflectedThetaCubicTrace pe a k =
      d*v*(z+star z)*(z*star z*(1-2*u)+v*(z-star z))/(1-z*star z) := by
  dsimp only
  rw [reflected_trace_normalization, reflectedResponse,
    reflected_trace _ _ _ _ (coherence_gap_ne (primeBurnolLogFrequency_pos pe) k.ne_zero)]
  simp only [primeBurnolReflectedCoherence, Complex.ofReal_pow, Complex.ofReal_mul]
  ring

theorem primeBurnolReflectedThetaCubicTrace_real_finitePart
    (pe : Nat.Primes × ℕ) (a : ℝ) :
    let d := primeBurnolReflectedPairMass pe
    let l := primeBurnolLogFrequency pe
    let u := primeBurnolThetaVisibility a pe.1^2
    let v := primeBurnolThetaVisibility a pe.1*primeBurnolThetaContrast a pe.1
    Tendsto (fun k => (primeBurnolReflectedThetaCubicTrace pe a k).re +
      2*d*v*(2*u-1)*l^2/(3*k^2)) (𝓝[≠] (0 : ℝ)) (𝓝 (14/3*d*v*(2*u-1))) := by
  dsimp only
  have h := (regularReal_limit (primeBurnolLogFrequency_pos pe)
    (primeBurnolThetaVisibility a pe.1^2)
    (primeBurnolThetaVisibility a pe.1*primeBurnolThetaContrast a pe.1)).const_mul
      (primeBurnolReflectedPairMass pe)
  convert h using 1 <;>
    simp [reflected_trace_normalization, Complex.mul_re] <;> ring_nf

theorem primeBurnolReflectedThetaCubicTrace_imag_finitePart
    (pe : Nat.Primes × ℕ) (a : ℝ) :
    let d := primeBurnolReflectedPairMass pe
    let l := primeBurnolLogFrequency pe
    let v := primeBurnolThetaVisibility a pe.1*primeBurnolThetaContrast a pe.1
    Tendsto (fun k => (primeBurnolReflectedThetaCubicTrace pe a k).im - 4*d*v^2*l/k)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  dsimp only
  have h := (regularImag_limit (primeBurnolLogFrequency_pos pe)
    (primeBurnolThetaVisibility a pe.1^2)
    (primeBurnolThetaVisibility a pe.1*primeBurnolThetaContrast a pe.1)).const_mul
      (primeBurnolReflectedPairMass pe)
  simp only [mul_zero] at h
  convert h using 1
  simp [reflected_trace_normalization, Complex.mul_im]
  ring_nf

/-- Every nonzero theta twist has an unbounded raw source response at clock collision. -/
theorem primeBurnolReflectedThetaCubicTrace_imag_atTop
    (pe : Nat.Primes × ℕ) (a : ℝˣ) :
    Tendsto (fun k => (primeBurnolReflectedThetaCubicTrace pe a k).im)
      (𝓝[>] (0 : ℝ)) atTop := by
  have hv : primeBurnolThetaVisibility a pe.1*primeBurnolThetaContrast a pe.1 ≠ 0 := by
    apply mul_ne_zero
    · exact one_div_ne_zero (Real.cosh_pos _).ne'
    · rw [primeBurnolThetaContrast, Real.tanh_eq_sinh_div_cosh]
      apply div_ne_zero _ (Real.cosh_pos _).ne'
      rw [Real.sinh_ne_zero]
      exact div_ne_zero (mul_ne_zero a.ne_zero
        (Real.log_pos (by exact_mod_cast pe.1.property.one_lt)).ne') (by norm_num)
  have h := imaginary_pole_atTop (primeBurnolLogFrequency_pos pe)
    (primeBurnolThetaVisibility a pe.1^2) hv
  have hs := Filter.Tendsto.const_mul_atTop (primeBurnolReflectedPairMass_pos pe) h
  simpa [reflected_trace_normalization, Complex.mul_im] using hs

end RHTower
