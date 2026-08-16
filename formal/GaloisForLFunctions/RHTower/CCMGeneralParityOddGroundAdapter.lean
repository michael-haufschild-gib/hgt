import GaloisForLFunctions.RHTower.CCMPublishedOddGroundRealZeros

/-!
# The parity-free odd ground of an arbitrary reflection-symmetric packet

The finite odd real-zero theorem needs nothing about the packet beyond three structural facts: the
matrix is positive semidefinite, it commutes with the centered reflection, and its commutator with
the clock is the rank-two skew form `|β⟩⟨η| − |η⟩⟨β|` built from the all-ones vector `η` and an odd
vector `β`.  Every such matrix splits into parity blocks whose cross commutator is exactly the
rank-one form required by the parity-free data, so a simple odd kernel vector produces the data and
therefore a band-limited Fourier transform with only real zeros.

The published restricted-Weil packet is one instance; the statements here are stated for an
arbitrary packet, which is what a compression of a truncated-convolution form supplies.
-/

open Matrix

open scoped Matrix ComplexOrder

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The abstract block construction -/

/-- **The parity-free odd ground data of an abstract block pair.**  Only positive semidefiniteness
of the two blocks, the rank-one cross commutator, and a simple visible odd kernel are used. -/
theorem exists_ccmParityFreeOddGroundData_of_blocks {even odd : Type*}
    [Fintype even] [Fintype odd] [DecidableEq even] [DecidableEq odd]
    {P : Matrix even even ℂ} {M : Matrix odd odd ℂ} {B : Matrix even odd ℂ}
    {eta : even → ℂ} {beta : odd → ℂ}
    (hP : P.PosSemidef) (hM : M.PosSemidef)
    (hcross : P * B - B * M = Matrix.vecMulVec eta (star beta))
    (c : odd → ℂ) (hMc : M *ᵥ c = 0)
    (hline : ∀ v : odd → ℂ, M *ᵥ v = 0 → ∃ z : ℂ, v = z • c)
    (hvisible : P *ᵥ (B *ᵥ c) ≠ 0) :
    ∃ S : CCMParityFreeOddGroundData even odd,
      S.Qplus = P ∧ S.Qminus = M ∧ S.frequency = B ∧ S.eta = eta ∧ S.beta = beta ∧
        ∃ s : ℂ, s ≠ 0 ∧ S.ground = s • c := by
  classical
  set delta : odd → ℂ := Bᴴ *ᵥ eta with hdelta
  set q : ℂ := star c ⬝ᵥ delta with hq_def
  have haction : P *ᵥ (B *ᵥ c) = (star beta ⬝ᵥ c) • eta := by
    have h := congrArg (fun X : Matrix even odd ℂ => X *ᵥ c) hcross
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hMc, Matrix.mulVec_zero, sub_zero, Matrix.vecMulVec_mulVec] at h
    simpa [smul_eq_mul, mul_comm] using h
  have hpair : star (B *ᵥ c) ⬝ᵥ eta = q := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have henergy_ne : star (B *ᵥ c) ⬝ᵥ (P *ᵥ (B *ᵥ c)) ≠ 0 := by
    intro hzero
    exact hvisible ((hP.dotProduct_mulVec_zero_iff (B *ᵥ c)).mp hzero)
  have hq : q ≠ 0 := by
    intro hqzero
    apply henergy_ne
    rw [haction, dotProduct_smul, hpair, hqzero]
    simp
  set s : ℂ := (star q)⁻¹ with hs_def
  have hs : s ≠ 0 := inv_ne_zero (star_ne_zero.mpr hq)
  set g : odd → ℂ := s • c with hg_def
  have hgkernel : M *ᵥ g = 0 := by
    rw [hg_def, Matrix.mulVec_smul, hMc, smul_zero]
  have hgline : ∀ v : odd → ℂ, M *ᵥ v = 0 → ∃ z : ℂ, v = z • g := by
    intro v hv
    obtain ⟨z, hz⟩ := hline v hv
    refine ⟨z * s⁻¹, ?_⟩
    rw [hz, hg_def, smul_smul]
    congr 1
    field_simp
  have hgnorm : star g ⬝ᵥ delta = 1 := by
    rw [hg_def]
    simp only [star_smul, smul_dotProduct]
    change star s * q = 1
    rw [hs_def]
    simp [hq]
  have hgvisible : P *ᵥ (B *ᵥ g) ≠ 0 := by
    intro hzero
    rw [hg_def, Matrix.mulVec_smul, Matrix.mulVec_smul] at hzero
    exact hvisible ((smul_eq_zero.mp hzero).resolve_left hs)
  exact
    ⟨{ Qplus := P
       Qminus := M
       frequency := B
       eta := eta
       beta := beta
       ground := g
       plus_posSemidef := hP
       minus_posSemidef := hM
       cross_commutator := hcross
       ground_kernel := hgkernel
       ground_radical := hgline
       frequency_ground_not_kernel := hgvisible
       normalized := hgnorm },
      rfl, rfl, rfl, rfl, rfl, s, hs, rfl⟩

/-! ## The parity blocks of an arbitrary reflection-commuting packet -/

/-- The even parity block of an arbitrary centered packet. -/
def ccmParityEvenBlockOf {N : ℕ}
    (Q : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ) :
    Matrix (CCMEvenParityIndex N) (CCMEvenParityIndex N) ℂ :=
  (ccmEvenParityFrame N)ᴴ * Q * ccmEvenParityFrame N

/-- The odd parity block of an arbitrary centered packet. -/
def ccmParityOddBlockOf {N : ℕ}
    (Q : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (ccmOddParityFrame N)ᴴ * Q * ccmOddParityFrame N

theorem ccmParityEvenBlockOf_posSemidef {N : ℕ}
    {Q : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ} (hQ : Q.PosSemidef) :
    (ccmParityEvenBlockOf Q).PosSemidef := by
  simpa only [ccmParityEvenBlockOf] using hQ.conjTranspose_mul_mul_same (ccmEvenParityFrame N)

theorem ccmParityOddBlockOf_posSemidef {N : ℕ}
    {Q : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ} (hQ : Q.PosSemidef) :
    (ccmParityOddBlockOf Q).PosSemidef := by
  simpa only [ccmParityOddBlockOf] using hQ.conjTranspose_mul_mul_same (ccmOddParityFrame N)

theorem ccmParity_mul_evenFrame_of_commutes {N : ℕ}
    {Q : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ}
    (hQ : Q * ccmParityReflectionMatrix N = ccmParityReflectionMatrix N * Q) :
    Q * ccmEvenParityFrame N = ccmEvenParityFrame N * ccmParityEvenBlockOf Q := by
  have hQE : ccmParityReflectionMatrix N * (Q * ccmEvenParityFrame N)
      = Q * ccmEvenParityFrame N := by
    calc ccmParityReflectionMatrix N * (Q * ccmEvenParityFrame N)
        = (ccmParityReflectionMatrix N * Q) * ccmEvenParityFrame N := by rw [Matrix.mul_assoc]
      _ = (Q * ccmParityReflectionMatrix N) * ccmEvenParityFrame N := by rw [hQ]
      _ = Q * (ccmParityReflectionMatrix N * ccmEvenParityFrame N) := by rw [Matrix.mul_assoc]
      _ = Q * ccmEvenParityFrame N := by rw [ccmParityReflectionMatrix_mul_evenFrame]
  have hcross : (ccmOddParityFrame N)ᴴ * (Q * ccmEvenParityFrame N) = 0 :=
    ccmOddFrame_conjTranspose_mul_eq_zero_of_even N _ hQE
  calc Q * ccmEvenParityFrame N
      = ccmEvenParityFrame N * ((ccmEvenParityFrame N)ᴴ * (Q * ccmEvenParityFrame N))
        + ccmOddParityFrame N * ((ccmOddParityFrame N)ᴴ * (Q * ccmEvenParityFrame N)) :=
        ccmParityFrames_reconstruct N (Q * ccmEvenParityFrame N)
    _ = ccmEvenParityFrame N * ccmParityEvenBlockOf Q := by
        rw [hcross]
        simp [ccmParityEvenBlockOf, Matrix.mul_assoc]

theorem ccmParity_mul_oddFrame_of_commutes {N : ℕ}
    {Q : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ}
    (hQ : Q * ccmParityReflectionMatrix N = ccmParityReflectionMatrix N * Q) :
    Q * ccmOddParityFrame N = ccmOddParityFrame N * ccmParityOddBlockOf Q := by
  have hQO : ccmParityReflectionMatrix N * (Q * ccmOddParityFrame N)
      = -(Q * ccmOddParityFrame N) := by
    calc ccmParityReflectionMatrix N * (Q * ccmOddParityFrame N)
        = (ccmParityReflectionMatrix N * Q) * ccmOddParityFrame N := by rw [Matrix.mul_assoc]
      _ = (Q * ccmParityReflectionMatrix N) * ccmOddParityFrame N := by rw [hQ]
      _ = Q * (ccmParityReflectionMatrix N * ccmOddParityFrame N) := by rw [Matrix.mul_assoc]
      _ = -(Q * ccmOddParityFrame N) := by
          rw [ccmParityReflectionMatrix_mul_oddFrame, Matrix.mul_neg]
  have hcross : (ccmEvenParityFrame N)ᴴ * (Q * ccmOddParityFrame N) = 0 :=
    ccmEvenFrame_conjTranspose_mul_eq_zero_of_odd N _ hQO
  calc Q * ccmOddParityFrame N
      = ccmEvenParityFrame N * ((ccmEvenParityFrame N)ᴴ * (Q * ccmOddParityFrame N))
        + ccmOddParityFrame N * ((ccmOddParityFrame N)ᴴ * (Q * ccmOddParityFrame N)) :=
        ccmParityFrames_reconstruct N (Q * ccmOddParityFrame N)
    _ = ccmOddParityFrame N * ccmParityOddBlockOf Q := by
        rw [hcross]
        simp [ccmParityOddBlockOf, Matrix.mul_assoc]

/-! ## The cross commutator of an arbitrary displacement packet -/

/-- **The rank-one cross commutator.**  If the packet commutes with the reflection and its clock
commutator is the rank-two skew form built from the all-ones vector and an odd vector, then its
parity blocks obey the rank-one cross commutator required by the parity-free data. -/
theorem ccmParityCross_commutator_of_displacement {N : ℕ}
    {Q : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ}
    {betaFull : CCMCenteredParityIndex N → ℂ}
    (hQ : Q * ccmParityReflectionMatrix N = ccmParityReflectionMatrix N * Q)
    (hbeta : ccmParityReflectionMatrix N *ᵥ betaFull = -betaFull)
    (hdisp : Q * ccmParityClockMatrix N - ccmParityClockMatrix N * Q
      = Matrix.vecMulVec (ccmPublishedParityEtaFull N) (star betaFull)
        - Matrix.vecMulVec betaFull (star (ccmPublishedParityEtaFull N))) :
    ccmParityEvenBlockOf Q * ccmPublishedParityCrossFrequency N
        - ccmPublishedParityCrossFrequency N * ccmParityOddBlockOf Q
      = Matrix.vecMulVec (ccmPublishedParityEta N)
          (star ((ccmOddParityFrame N)ᴴ *ᵥ betaFull)) := by
  set E := ccmEvenParityFrame N with hE
  set O := ccmOddParityFrame N with hO
  set D := ccmParityClockMatrix N with hD
  set P := ccmParityEvenBlockOf Q with hP
  set M := ccmParityOddBlockOf Q with hM
  set B := ccmPublishedParityCrossFrequency N with hB
  have hQE : Q * E = E * P := ccmParity_mul_evenFrame_of_commutes hQ
  have hQO : Q * O = O * M := ccmParity_mul_oddFrame_of_commutes hQ
  have hDO : D * O = E * B := ccmParityClockMatrix_mul_oddFrame N
  have hEE : Eᴴ * E = 1 := ccmEvenParityFrame_orthonormal N
  have hfirst : Eᴴ * (Q * D) * O = P * B := by
    calc Eᴴ * (Q * D) * O = Eᴴ * (Q * (D * O)) := by simp only [Matrix.mul_assoc]
      _ = Eᴴ * (Q * (E * B)) := by rw [hDO]
      _ = Eᴴ * ((Q * E) * B) := by rw [Matrix.mul_assoc]
      _ = Eᴴ * ((E * P) * B) := by rw [hQE]
      _ = (Eᴴ * E) * (P * B) := by simp only [Matrix.mul_assoc]
      _ = P * B := by rw [hEE, Matrix.one_mul]
  have hsecond : Eᴴ * (D * Q) * O = B * M := by
    calc Eᴴ * (D * Q) * O = Eᴴ * (D * (Q * O)) := by simp only [Matrix.mul_assoc]
      _ = Eᴴ * (D * (O * M)) := by rw [hQO]
      _ = Eᴴ * ((D * O) * M) := by rw [Matrix.mul_assoc]
      _ = Eᴴ * ((E * B) * M) := by rw [hDO]
      _ = (Eᴴ * E) * (B * M) := by simp only [Matrix.mul_assoc]
      _ = B * M := by rw [hEE, Matrix.one_mul]
  have hbetaOddFrame : star betaFull ᵥ* O = star (Oᴴ *ᵥ betaFull) := by
    have h := Matrix.star_mulVec Oᴴ betaFull
    change star betaFull ᵥ* O = star (Oᴴ *ᵥ betaFull)
    simpa only [Matrix.conjTranspose_conjTranspose] using h.symm
  have hetaOddFrame : star (ccmPublishedParityEtaFull N) ᵥ* O = 0 :=
    star_ccmPublishedParityEtaFull_vecMul_oddFrame N
  have hetaEvenFrame : Eᴴ *ᵥ ccmPublishedParityEtaFull N = ccmPublishedParityEta N := rfl
  have hbetaEvenFrame : Eᴴ *ᵥ betaFull = 0 :=
    ccmEvenFrame_conjTranspose_mulVec_eq_zero_of_odd N betaFull hbeta
  have hproject := congrArg (fun X => Eᴴ * X * O) hdisp
  rw [Matrix.mul_sub, Matrix.sub_mul, hfirst, hsecond,
    Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    hetaEvenFrame, hbetaOddFrame, hbetaEvenFrame, hetaOddFrame,
    Matrix.zero_vecMulVec, sub_zero] at hproject
  exact hproject

/-! ## The full adapter -/

/-- **Every reflection-symmetric displacement packet with a simple odd kernel carries the
parity-free odd ground data.** -/
theorem exists_ccmParityFreeOddGroundData_of_simple_odd_ground {N : ℕ}
    {Q : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ}
    {betaFull : CCMCenteredParityIndex N → ℂ}
    (hQpsd : Q.PosSemidef)
    (hQ : Q * ccmParityReflectionMatrix N = ccmParityReflectionMatrix N * Q)
    (hbeta : ccmParityReflectionMatrix N *ᵥ betaFull = -betaFull)
    (hdisp : Q * ccmParityClockMatrix N - ccmParityClockMatrix N * Q
      = Matrix.vecMulVec (ccmPublishedParityEtaFull N) (star betaFull)
        - Matrix.vecMulVec betaFull (star (ccmPublishedParityEtaFull N)))
    (c : Fin N → ℂ) (hc : c ≠ 0)
    (hground : Q *ᵥ (ccmOddParityFrame N *ᵥ c) = 0)
    (hline : ∀ v : CCMCenteredParityIndex N → ℂ, Q *ᵥ v = 0 →
      ∃ z : ℂ, v = z • (ccmOddParityFrame N *ᵥ c)) :
    ∃ S : CCMParityFreeOddGroundData (CCMEvenParityIndex N) (Fin N),
      S.Qplus = ccmParityEvenBlockOf Q ∧ S.Qminus = ccmParityOddBlockOf Q ∧
        S.frequency = ccmPublishedParityCrossFrequency N ∧
        S.eta = ccmPublishedParityEta N ∧
        ∃ s : ℂ, s ≠ 0 ∧ S.ground = s • c := by
  classical
  set E := ccmEvenParityFrame N with hE
  set O := ccmOddParityFrame N with hO
  set P := ccmParityEvenBlockOf Q with hPdef
  set M := ccmParityOddBlockOf Q with hMdef
  set B := ccmPublishedParityCrossFrequency N with hBdef
  have hQO : Q * O = O * M := ccmParity_mul_oddFrame_of_commutes hQ
  have hQE : Q * E = E * P := ccmParity_mul_evenFrame_of_commutes hQ
  have hEE : Eᴴ * E = 1 := ccmEvenParityFrame_orthonormal N
  have hEO : Eᴴ * O = 0 := ccmParityFrames_orthogonal N
  have hMc : M *ᵥ c = 0 := by
    apply ccmOddParityFrame_mulVec_injective N
    calc O *ᵥ (M *ᵥ c) = (O * M) *ᵥ c := by rw [← Matrix.mulVec_mulVec]
      _ = (Q * O) *ᵥ c := by rw [hQO]
      _ = Q *ᵥ (O *ᵥ c) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := hground
      _ = O *ᵥ 0 := by rw [Matrix.mulVec_zero]
  have hMline : ∀ v : Fin N → ℂ, M *ᵥ v = 0 → ∃ z : ℂ, v = z • c := by
    intro v hv
    have hfull : Q *ᵥ (O *ᵥ v) = 0 := by
      calc Q *ᵥ (O *ᵥ v) = (Q * O) *ᵥ v := by rw [← Matrix.mulVec_mulVec]
        _ = (O * M) *ᵥ v := by rw [hQO]
        _ = O *ᵥ (M *ᵥ v) := by rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [hv, Matrix.mulVec_zero]
    obtain ⟨z, hz⟩ := hline (O *ᵥ v) hfull
    refine ⟨z, ccmOddParityFrame_mulVec_injective N ?_⟩
    change O *ᵥ v = O *ᵥ (z • c)
    rw [Matrix.mulVec_smul]
    exact hz
  have hvisible : P *ᵥ (B *ᵥ c) ≠ 0 := by
    intro hPB
    have hfullEven : Q *ᵥ (E *ᵥ (B *ᵥ c)) = 0 := by
      calc Q *ᵥ (E *ᵥ (B *ᵥ c)) = (Q * E) *ᵥ (B *ᵥ c) := by rw [← Matrix.mulVec_mulVec]
        _ = (E * P) *ᵥ (B *ᵥ c) := by rw [hQE]
        _ = E *ᵥ (P *ᵥ (B *ᵥ c)) := (Matrix.mulVec_mulVec (B *ᵥ c) E P).symm
        _ = 0 := by rw [hPB, Matrix.mulVec_zero]
    obtain ⟨z, hz⟩ := hline (E *ᵥ (B *ᵥ c)) hfullEven
    have hBc : B *ᵥ c = 0 := by
      have hleft : Eᴴ *ᵥ (E *ᵥ (B *ᵥ c)) = B *ᵥ c := by
        rw [Matrix.mulVec_mulVec, hEE, Matrix.one_mulVec]
      have hright : Eᴴ *ᵥ (z • (O *ᵥ c)) = 0 := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hEO, Matrix.zero_mulVec, smul_zero]
      have hzproj := congrArg (fun v => Eᴴ *ᵥ v) hz
      rw [hleft, hright] at hzproj
      exact hzproj
    apply hc
    apply ccmPublishedParityCrossFrequency_mulVec_injective N
    simpa only [hBdef, Matrix.mulVec_zero] using hBc
  have hcross := ccmParityCross_commutator_of_displacement hQ hbeta hdisp
  obtain ⟨S, hQp, hQm, hfreq, heta, _, hscale⟩ :=
    exists_ccmParityFreeOddGroundData_of_blocks
      (ccmParityEvenBlockOf_posSemidef hQpsd) (ccmParityOddBlockOf_posSemidef hQpsd)
      hcross c hMc hMline hvisible
  exact ⟨S, hQp, hQm, hfreq, heta, hscale⟩

/-! ## Rescaling the ground does not move the Fourier zeros -/

theorem ccmOddGroundCoeffAux_smul (N : ℕ) (s : ℂ) (c : Fin N → ℂ) (n : ℕ) :
    ccmOddGroundCoeffAux N (s • c) n = s * ccmOddGroundCoeffAux N c n := by
  rw [ccmOddGroundCoeffAux, ccmOddGroundCoeffAux]
  by_cases h : n < N
  · rw [dif_pos h, dif_pos h, Pi.smul_apply, smul_eq_mul]
  · rw [dif_neg h, dif_neg h, mul_zero]

theorem ccmOddGroundCoeff_smul (N : ℕ) (s : ℂ) (c : Fin N → ℂ) (j : ℤ) :
    ccmOddGroundCoeff N (s • c) j = s * ccmOddGroundCoeff N c j := by
  rw [ccmOddGroundCoeff, ccmOddGroundCoeff]
  by_cases h1 : 0 < j
  · rw [if_pos h1, if_pos h1, ccmOddGroundCoeffAux_smul]
    ring
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : j < 0
    · rw [if_pos h2, if_pos h2, ccmOddGroundCoeffAux_smul]
      ring
    · rw [if_neg h2, if_neg h2, mul_zero]

theorem ccmTrigPoly_smul (N : ℕ) (s : ℂ) (c : Fin N → ℂ) (x : ℝ) :
    ccmTrigPoly N (ccmOddGroundCoeff N (s • c)) x
      = s * ccmTrigPoly N (ccmOddGroundCoeff N c) x := by
  rw [ccmTrigPoly, ccmTrigPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ccmOddGroundCoeff_smul]
  ring

theorem compactFourier_ccmTrigPoly_smul (N : ℕ) (s : ℂ) (c : Fin N → ℂ) (z : ℂ) :
    compactFourier (ccmTrigPoly N (ccmOddGroundCoeff N (s • c))) 0 (2 * Real.pi) z
      = s * compactFourier (ccmTrigPoly N (ccmOddGroundCoeff N c)) 0 (2 * Real.pi) z := by
  rw [compactFourier, compactFourier, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [ccmTrigPoly_smul]
  ring

/-! ## The general finite odd real-zero theorem -/

/-- **The finite odd theorem for an arbitrary reflection-symmetric displacement packet.**  Every
zero of the band-limited Fourier transform of the odd kernel vector is real. -/
theorem ccmGeneralParityOddGround_compactFourier_zero_im_eq_zero {N : ℕ}
    {Q : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ}
    {betaFull : CCMCenteredParityIndex N → ℂ}
    (hQpsd : Q.PosSemidef)
    (hQ : Q * ccmParityReflectionMatrix N = ccmParityReflectionMatrix N * Q)
    (hbeta : ccmParityReflectionMatrix N *ᵥ betaFull = -betaFull)
    (hdisp : Q * ccmParityClockMatrix N - ccmParityClockMatrix N * Q
      = Matrix.vecMulVec (ccmPublishedParityEtaFull N) (star betaFull)
        - Matrix.vecMulVec betaFull (star (ccmPublishedParityEtaFull N)))
    {c : Fin N → ℂ} (hc : c ≠ 0)
    (hground : Q *ᵥ (ccmOddParityFrame N *ᵥ c) = 0)
    (hline : ∀ v : CCMCenteredParityIndex N → ℂ, Q *ᵥ v = 0 →
      ∃ z : ℂ, v = z • (ccmOddParityFrame N *ᵥ c))
    {z : ℂ}
    (hzero : compactFourier (ccmTrigPoly N (ccmOddGroundCoeff N c)) 0 (2 * Real.pi) z = 0) :
    z.im = 0 := by
  obtain ⟨S, _, _, hfreq, heta, s, hs, hground'⟩ :=
    exists_ccmParityFreeOddGroundData_of_simple_odd_ground hQpsd hQ hbeta hdisp c hc hground hline
  refine ccmParityFreeOddGroundData_compactFourier_zero_im_eq_zero S hfreq heta ?_
  rw [hground', compactFourier_ccmTrigPoly_smul, hzero, mul_zero]

/-! ## The general centered divided-difference packet -/

/-- The complexified spectral-floor shift of a centered divided-difference matrix: the general
finite packet of the parity-free theorem. -/
def ccmCenteredParityPacket {N : ℕ} (source diagonal : CCMCenteredParityIndex N → ℝ) (mu : ℝ) :
    Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ :=
  (ccmScalarShift (ccmDividedDifferenceMatrix (ccmParityCenteredClock N) source diagonal) mu).map
    (algebraMap ℝ ℂ)

/-- The complexified source vector of the packet. -/
def ccmCenteredParitySourceFull {N : ℕ} (source : CCMCenteredParityIndex N → ℝ) :
    CCMCenteredParityIndex N → ℂ := fun i => (source i : ℂ)

theorem ccmCenteredParityPacket_commutes_reflection {N : ℕ}
    {source diagonal : CCMCenteredParityIndex N → ℝ} (mu : ℝ)
    (hsource : ∀ i, source (ccmCenteredParityReflection N i) = -source i)
    (hdiagonal : ∀ i, diagonal (ccmCenteredParityReflection N i) = diagonal i) :
    ccmCenteredParityPacket source diagonal mu * ccmParityReflectionMatrix N
      = ccmParityReflectionMatrix N * ccmCenteredParityPacket source diagonal mu := by
  have hQ := ccmReflectionMatrix_commutes_dividedDifference
    (ccmCenteredParityReflection N) (ccmCenteredParityReflection_involutive N)
    (ccmParityCenteredClock N) source diagonal
    (ccmParityCenteredClock_reflection N) hsource hdiagonal
  have hshift := ccmScalarShift_commutes _ _ mu hQ
  have hmap := congrArg (fun M : Matrix (CCMCenteredParityIndex N)
    (CCMCenteredParityIndex N) ℝ => M.map (algebraMap ℝ ℂ)) hshift
  simpa only [ccmCenteredParityPacket, ccmParityReflectionMatrix, ← Matrix.map_mul] using hmap

theorem ccmCenteredParitySourceFull_odd {N : ℕ}
    {source : CCMCenteredParityIndex N → ℝ}
    (hsource : ∀ i, source (ccmCenteredParityReflection N i) = -source i) :
    ccmParityReflectionMatrix N *ᵥ ccmCenteredParitySourceFull source
      = -ccmCenteredParitySourceFull source := by
  funext i
  rw [ccmParityReflectionMatrix_mulVec_apply]
  simp only [ccmCenteredParitySourceFull, Pi.neg_apply]
  rw [hsource i]
  push_cast
  ring

theorem ccmCenteredParityPacket_displacement {N : ℕ}
    (source diagonal : CCMCenteredParityIndex N → ℝ) (mu : ℝ) :
    ccmCenteredParityPacket source diagonal mu * ccmParityClockMatrix N
        - ccmParityClockMatrix N * ccmCenteredParityPacket source diagonal mu
      = Matrix.vecMulVec (ccmPublishedParityEtaFull N)
            (star (ccmCenteredParitySourceFull source))
          - Matrix.vecMulVec (ccmCenteredParitySourceFull source)
            (star (ccmPublishedParityEtaFull N)) := by
  have hbase := ccmDividedDifference_displacement (ccmParityCenteredClock N) source diagonal
    (ccmParityCenteredClock_injective N)
  have hneg := ccmScalarShift_displacement
    (ccmDividedDifferenceMatrix (ccmParityCenteredClock N) source diagonal)
    (ccmDiagonalClock (ccmParityCenteredClock N))
    (Matrix.vecMulVec source ccmConstantBoundary
      - Matrix.vecMulVec ccmConstantBoundary source) mu hbase
  have hshift := congrArg (fun M : Matrix (CCMCenteredParityIndex N)
    (CCMCenteredParityIndex N) ℝ => -M) hneg
  simp only [neg_sub] at hshift
  have hmap := congrArg (fun M : Matrix (CCMCenteredParityIndex N)
    (CCMCenteredParityIndex N) ℝ => M.map (algebraMap ℝ ℂ)) hshift
  have hRmap : (Matrix.vecMulVec ccmConstantBoundary source
        - Matrix.vecMulVec source (ccmConstantBoundary
            (n := CCMCenteredParityIndex N))).map (algebraMap ℝ ℂ)
      = Matrix.vecMulVec (ccmPublishedParityEtaFull N)
            (star (ccmCenteredParitySourceFull source))
          - Matrix.vecMulVec (ccmCenteredParitySourceFull source)
            (star (ccmPublishedParityEtaFull N)) := by
    ext i j
    simp [Matrix.vecMulVec_apply, ccmConstantBoundary,
      ccmPublishedParityEtaFull, ccmCenteredParitySourceFull]
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, hRmap] at hmap
  simpa only [ccmParityClockMatrix, ccmCenteredParityPacket] using hmap

/-- **Section 1 of the parity-free law, in full generality.**  Let `Q` be a real symmetric
divided-difference matrix on the centered index set, with an odd source, an arbitrary
reflection-even diagonal and any spectral-floor shift making it positive semidefinite.  If its
kernel is the line spanned by a single odd vector, then the band-limited Fourier transform of that
vector has only real zeros. -/
theorem ccmCenteredDividedDifferenceOddGround_compactFourier_zero_im_eq_zero {N : ℕ}
    {source diagonal : CCMCenteredParityIndex N → ℝ} {mu : ℝ}
    (hsource : ∀ i, source (ccmCenteredParityReflection N i) = -source i)
    (hdiagonal : ∀ i, diagonal (ccmCenteredParityReflection N i) = diagonal i)
    (hpsd : (ccmCenteredParityPacket source diagonal mu).PosSemidef)
    {c : Fin N → ℂ} (hc : c ≠ 0)
    (hground : ccmCenteredParityPacket source diagonal mu *ᵥ (ccmOddParityFrame N *ᵥ c) = 0)
    (hline : ∀ v : CCMCenteredParityIndex N → ℂ,
      ccmCenteredParityPacket source diagonal mu *ᵥ v = 0 →
        ∃ z : ℂ, v = z • (ccmOddParityFrame N *ᵥ c))
    {z : ℂ}
    (hzero : compactFourier (ccmTrigPoly N (ccmOddGroundCoeff N c)) 0 (2 * Real.pi) z = 0) :
    z.im = 0 :=
  ccmGeneralParityOddGround_compactFourier_zero_im_eq_zero hpsd
    (ccmCenteredParityPacket_commutes_reflection mu hsource hdiagonal)
    (ccmCenteredParitySourceFull_odd hsource)
    (ccmCenteredParityPacket_displacement source diagonal mu) hc hground hline hzero

/-- **Section 4 of the parity-free law, in full generality.**  A mean-square limit of odd kernel
vectors of general centered divided-difference packets, with a nonvanishing band-limited Fourier
transform, again has only real Fourier zeros. -/
theorem ccmCenteredDividedDifferenceOddGroundLimit_compactFourier_zero_im_eq_zero
    {N : ℕ → ℕ} {source diagonal : ∀ n : ℕ, CCMCenteredParityIndex (N n) → ℝ} {mu : ℕ → ℝ}
    (hsource : ∀ n i, source n (ccmCenteredParityReflection (N n) i) = -source n i)
    (hdiagonal : ∀ n i, diagonal n (ccmCenteredParityReflection (N n) i) = diagonal n i)
    (hpsd : ∀ n, (ccmCenteredParityPacket (source n) (diagonal n) (mu n)).PosSemidef)
    (c : ∀ n : ℕ, Fin (N n) → ℂ) (hc : ∀ n, c n ≠ 0)
    (hground : ∀ n, ccmCenteredParityPacket (source n) (diagonal n) (mu n)
      *ᵥ (ccmOddParityFrame (N n) *ᵥ c n) = 0)
    (hline : ∀ n, ∀ v : CCMCenteredParityIndex (N n) → ℂ,
      ccmCenteredParityPacket (source n) (diagonal n) (mu n) *ᵥ v = 0 →
        ∃ z : ℂ, v = z • (ccmOddParityFrame (N n) *ᵥ c n))
    (f : ℝ → ℂ) (hf : Continuous f)
    (hmean : Filter.Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..(2 * Real.pi),
        ‖ccmTrigPoly (N n) (ccmOddGroundCoeff (N n) (c n)) x - f x‖ ^ 2)
      Filter.atTop (nhds 0))
    {w z : ℂ} (hw : compactFourier f 0 (2 * Real.pi) w ≠ 0)
    (hz : compactFourier f 0 (2 * Real.pi) z = 0) :
    z.im = 0 := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  refine compactFourier_limit_zero_im_eq_zero_of_meanSquare
    (fun n => ccmTrigPoly (N n) (ccmOddGroundCoeff (N n) (c n))) f
    (fun n => continuous_ccmTrigPoly _ _) hf hpi hmean ?_ hw hz
  intro n u hu
  exact ccmCenteredDividedDifferenceOddGround_compactFourier_zero_im_eq_zero
    (hsource n) (hdiagonal n) (hpsd n) (hc n) (hground n) (hline n) hu

end

end RHTower
