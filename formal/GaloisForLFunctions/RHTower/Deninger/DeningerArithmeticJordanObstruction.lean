import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticGelfandTriple

/-!
# Source Jordan chains and the Hodge simplicity obstruction

Every positive-depth Xi divided chain is nonzero in the source quotient, not merely the terminal
chain.  The proof is intrinsic: if a divided chain were an Xi coboundary, exact partial
factorization and injectivity of Xi multiplication would make a positive power of `z - rho`
invertible as an entire function, contradicted by evaluation at `rho`.

Consequently a Xi zero of multiplicity at least two supplies a genuine length-two Jordan chain in
compact-open source cohomology.  A positive weight-one Hodge star excludes such a chain.  Thus the
direct strong-dual Hodge model would imply simplicity of every Xi zero in addition to RH.  This
formalizes the precise extra burden carried by the cyclic quotient `O(C)/(XiC)`.
-/

namespace RHTower

noncomputable section

/-- Entire source `(z - alpha)^k`. -/
def deningerEntireCenteredPower
    (alpha : ℂ) (k : ℕ) : DeningerEntire :=
  (deningerEntireCoordinate -
    algebraMap ℂ DeningerEntire alpha) ^ k

@[simp]
theorem deningerEntireCenteredPower_apply
    (alpha z : ℂ) (k : ℕ) :
    deningerEntireCenteredPower alpha k z =
      (z - alpha) ^ k := by
  simp [deningerEntireCenteredPower]

/-- Every divided chain of depth `1 ≤ k ≤ multiplicity` is nonzero in algebraic source `H¹`. -/
theorem deningerEntireDividedChainClass_ne_zero
    (rho : XiDivisorSupport) {k : ℕ}
    (hk0 : 0 < k)
    (hkm : k ≤ xiSupportMultiplicity rho) :
    deningerEntireDividedChainClass
      (xiSpectralPointSupport rho) k ≠ 0 := by
  intro hzero
  have hmem :
      deningerEntireDividedChain
          (xiSpectralPointSupport rho) k ∈
        deningerEntireXiIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [deningerEntireXiIdeal,
    Ideal.mem_span_singleton'] at hmem
  obtain ⟨G, hG⟩ := hmem
  let P : DeningerEntire :=
    deningerEntireCenteredPower
      (xiSpectralPointSupport rho) k
  have hfactor :
      deningerEntireXi =
        P * deningerEntireDividedChain
          (xiSpectralPointSupport rho) k := by
    apply DeningerEntire.ext
    intro z
    exact
      xiThetaDividedChain_partial_factorization
        rho hkm z
  have htotal :
      deningerEntireXi * (1 : DeningerEntire) =
        deningerEntireXi * (P * G) := by
    calc
      deningerEntireXi * (1 : DeningerEntire) =
          deningerEntireXi := mul_one _
      _ = P * deningerEntireDividedChain
          (xiSpectralPointSupport rho) k := hfactor
      _ = P * (G * deningerEntireXi) := by rw [hG]
      _ = deningerEntireXi * (P * G) := by ring
  have hcancel :
      (1 : DeningerEntire) = P * G :=
    deningerEntireXi_mul_injective htotal
  have heval :=
    congrArg
      (fun F : DeningerEntire =>
        F (xiSpectralPointSupport rho))
      hcancel
  simp [P, deningerEntireCenteredPower,
    hk0.ne'] at heval

/-- Every positive-depth divided chain is also nonzero in compact-open source `H¹`. -/
theorem deningerCompactOpenDividedChainClass_ne_zero
    (rho : XiDivisorSupport) {k : ℕ}
    (hk0 : 0 < k)
    (hkm : k ≤ xiSupportMultiplicity rho) :
    deningerCompactOpenDividedChainClass
      (xiSpectralPointSupport rho) k ≠ 0 := by
  intro hzero
  have hmem :
      deningerCompactOpenDividedChain
          (xiSpectralPointSupport rho) k ∈
        deningerCompactOpenXiRange :=
    (DeningerCompactOpenQuotient.mk_eq_zero_iff_mem
      deningerCompactOpenXiRange
      (deningerCompactOpenDividedChain
        (xiSpectralPointSupport rho) k)).mp hzero
  obtain ⟨G, hG⟩ := hmem
  apply
    deningerEntireDividedChainClass_ne_zero
      rho hk0 hkm
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [deningerEntireXiIdeal,
    Ideal.mem_span_singleton']
  refine ⟨deningerCompactOpenEntireEquiv G, ?_⟩
  have heq :=
    congrArg deningerCompactOpenEntireEquiv hG
  change
    deningerEntireXi *
        deningerCompactOpenEntireEquiv G =
      deningerEntireDividedChain
        (xiSpectralPointSupport rho) k at heq
  simpa [mul_comm] using heq

namespace DeningerArithmeticTopologicalHodgeStar

/-- A positive topological weight-one Hodge star excludes a nontrivial length-two Jordan chain. -/
theorem jordan_chain_head_eq_zero
    (Hodge : DeningerArithmeticTopologicalHodgeStar)
    {lambda : ℂ}
    {u v : DeningerArithmeticCompactOpenH1}
    (hu :
      deningerCompactOpenTheta u = lambda • u)
    (hv :
      deningerCompactOpenTheta v =
        lambda • v + u) :
    u = 0 := by
  by_contra hu0
  have hre :=
    Hodge.eigenvalue_re_eq_half hu0 hu
  have hweight :
      lambda + starRingEnd ℂ lambda = 1 := by
    apply Complex.ext
    · simp [hre]
      norm_num
    · simp
  have hcup :=
    deningerCompactOpenTheta_poincare
      v (Hodge.star u)
  rw [hv, Hodge.theta_star, hu] at hcup
  have hstar :
      Hodge.star (lambda • u) =
        starRingEnd ℂ lambda • Hodge.star u :=
    map_smulₛₗ Hodge.star lambda u
  rw [hstar] at hcup
  change
    Hodge.star u (lambda • v + u) +
        (starRingEnd ℂ lambda • Hodge.star u) v =
      Hodge.star u v at hcup
  simp only [map_add, map_smul,
    _root_.smul_apply] at hcup
  have huu : Hodge.star u u = 0 := by
    linear_combination hcup -
      Hodge.star u v * hweight
  have hpos := Hodge.positive hu0
  rw [huu] at hpos
  simp at hpos

/--
A direct positive Hodge star on the cyclic entire quotient forces every Xi zero to be simple.
-/
theorem xiSupportMultiplicity_eq_one
    (Hodge : DeningerArithmeticTopologicalHodgeStar)
    (rho : XiDivisorSupport) :
    xiSupportMultiplicity rho = 1 := by
  have hmpos := xiSupportMultiplicity_pos rho
  by_contra hne
  have hm2 : 2 ≤ xiSupportMultiplicity rho := by
    omega
  let base :
      DeningerArithmeticCompactOpenH1 :=
    deningerCompactOpenDividedChainClass
      (xiSpectralPointSupport rho) 1
  let head :
      DeningerArithmeticCompactOpenH1 :=
    Complex.I • base
  let generalized :
      DeningerArithmeticCompactOpenH1 :=
    deningerCompactOpenDividedChainClass
      (xiSpectralPointSupport rho) 2
  let lambda : ℂ :=
    1 / 2 + Complex.I *
      xiSpectralPointSupport rho
  have hbase0 : base ≠ 0 :=
    deningerCompactOpenDividedChainClass_ne_zero
      rho (by omega) (by omega)
  have hhead0 : head ≠ 0 :=
    smul_ne_zero Complex.I_ne_zero hbase0
  have hbaseEigen :
      deningerCompactOpenTheta base =
        lambda • base := by
    dsimp only [base, lambda]
    rw [deningerCompactOpenTheta_dividedChainClass
      rho (xiSupportMultiplicity_pos rho)]
    rw [deningerCompactOpenDividedChainClass_zero]
    simp
  have hheadEigen :
      deningerCompactOpenTheta head =
        lambda • head := by
    dsimp only [head]
    rw [map_smul, hbaseEigen]
    simp [smul_smul, mul_comm]
  have hgeneralized :
      deningerCompactOpenTheta generalized =
        lambda • generalized + head := by
    dsimp only [generalized, lambda, head, base]
    exact
      deningerCompactOpenTheta_dividedChainClass
        rho (by omega)
  exact hhead0
    (Hodge.jordan_chain_head_eq_zero
      hheadEigen hgeneralized)

end DeningerArithmeticTopologicalHodgeStar

end

end RHTower
