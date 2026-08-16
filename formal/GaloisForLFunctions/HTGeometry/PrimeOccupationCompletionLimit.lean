import GaloisForLFunctions.HTGeometry.PrimeOccupationCompletionProduct
import GaloisForLFunctions.HTGeometry.PrimePowerOccupationHypertranscendence
import GaloisForLFunctions.HTGeometry.PrimeOccupationCofinalLimit
import GaloisForLFunctions.HTGeometry.OccupationEulerProduct

/-!
# Cofinal completion of the prime occupation product

The occupation modes of a finite prime packet are the exponent vectors supported in the packet, and
unique factorization identifies all occupation vectors with the positive integers.  Reading the
completed product `∏_{n ≥ 1}(1 - x/n^r)` in that indexing and comparing the two products by the
total distance of their factors turns the cofinal exhaustion of the primes into convergence of the
packet products.

Together with the hypertranscendence of every packet at every positive integer temperature and the
differential algebraicity of the completion at even temperature, this is the exact statement that a
normally convergent net of hypertranscendental functions can have a differentially algebraic limit.
-/

namespace GaloisForLFunctions

open HTGeometry Filter Topology

noncomputable section

/-- Unique factorization as an equivalence between occupation vectors and positive integers. -/
def occupationEquivNatPos : (Nat.Primes →₀ ℕ) ≃ {n : ℕ // n ≠ 0} where
  toFun ν := ⟨primeProduct ν, (primeProduct_pos ν).ne'⟩
  invFun n := primeExponentVector (n : ℕ)
  left_inv ν := primeProduct_injective (primeProduct_primeExponentVector (primeProduct_pos ν).ne')
  right_inv n := Subtype.ext (primeProduct_primeExponentVector n.2)


/-- The centred factor of the occupation product at temperature `r`. -/
def occupationFactor (r : ℕ) (x : ℂ) (ν : Nat.Primes →₀ ℕ) : ℂ := -(x * occupationRecip ν ^ r)

theorem occFull_primeProduct {r : ℕ} (x : ℂ) (ν : Nat.Primes →₀ ℕ) :
    HTGeometry.occFull r x (primeProduct ν) = occupationFactor r x ν := by
  have h0 : primeProduct ν ≠ 0 := (primeProduct_pos ν).ne'
  rw [HTGeometry.occFull, if_neg h0, occupationFactor, occupationRecip_eq, inv_pow,
    div_eq_mul_inv]

/-- **The completed product, indexed by occupation vectors.** -/
theorem hasProd_occupationProduct_occ {r : ℕ} (hr : 2 ≤ r) (x : ℂ) :
    HasProd (fun ν : Nat.Primes →₀ ℕ => 1 + occupationFactor r x ν)
      (HTGeometry.occupationProduct r x) := by
  have hbase := HTGeometry.hasProd_occFull hr x
  have hinj : Function.Injective (fun n : {n : ℕ // n ≠ 0} => (n : ℕ)) := Subtype.val_injective
  have hout : ∀ m ∉ Set.range (fun n : {n : ℕ // n ≠ 0} => (n : ℕ)),
      (1 : ℂ) + HTGeometry.occFull r x m = 1 := by
    intro m hm
    have hm0 : m = 0 := by
      by_contra h
      exact hm ⟨⟨m, h⟩, rfl⟩
    rw [hm0, HTGeometry.occFull, if_pos rfl, add_zero]
  have hsub : HasProd (fun n : {n : ℕ // n ≠ 0} => 1 + HTGeometry.occFull r x (n : ℕ))
      (HTGeometry.occupationProduct r x) := (hinj.hasProd_iff hout).mpr hbase
  have hre := (occupationEquivNatPos.hasProd_iff
    (f := fun n : {n : ℕ // n ≠ 0} => 1 + HTGeometry.occFull r x (n : ℕ))).mpr hsub
  refine hre.congr_fun fun ν => ?_
  simp only [Function.comp_apply]
  rw [show ((occupationEquivNatPos ν : {n : ℕ // n ≠ 0}) : ℕ) = primeProduct ν from rfl,
    occFull_primeProduct]


/-- Packet-supported occupation vectors are exactly the exponent vectors on the packet. -/
def occupationSupportedEquiv (S : Finset Nat.Primes) :
    ↥(occupationSupported S) ≃ (↥S →₀ ℕ) :=
  (Equiv.subtypeEquivRight (fun ν : Nat.Primes →₀ ℕ => by
      constructor
      · intro h
        exact Finset.coe_subset.mpr h
      · intro h
        exact Finset.coe_subset.mp h)).trans
    (Finsupp.restrictSupportEquiv (α := Nat.Primes) (↑S : Set Nat.Primes) ℕ)

theorem occupationRecip_extendDomain_pow {S : Finset Nat.Primes} (r : ℕ) (ν : ↥S →₀ ℕ) :
    occupationRecip (Finsupp.extendDomain (P := fun p => p ∈ (↑S : Set Nat.Primes)) ν) ^ r
      = HTGeometry.nomeMonomial (fun p : ↥S => primePowerNome r (p : Nat.Primes)) ν := by
  classical
  rw [occupationRecip, HTGeometry.nomeMonomial, HTGeometry.nomeMonomial,
    Finsupp.extendDomain_eq_embDomain_subtype, Finsupp.prod_embDomain, Finsupp.prod, Finsupp.prod,
    ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [primePowerNome, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rfl

theorem primeOccupationFacePow_eq_tprod_occ (r : ℕ) (S : Finset Nat.Primes) (x : ℂ) :
    primeOccupationFacePow r S x
      = ∏' ν : ↥(occupationSupported S), (1 + occupationFactor r x (ν : Nat.Primes →₀ ℕ)) := by
  classical
  rw [primeOccupationFacePow_eq_tprod]
  rw [← (occupationSupportedEquiv S).tprod_eq
    (fun ν : ↥S →₀ ℕ =>
      1 - x * HTGeometry.nomeMonomial
        (fun p : ↥S => primePowerNome r (p : Nat.Primes)) ν)]
  refine tprod_congr fun ν' => ?_
  have hext : Finsupp.extendDomain (P := fun p => p ∈ (↑S : Set Nat.Primes))
      (occupationSupportedEquiv S ν') = (ν' : Nat.Primes →₀ ℕ) :=
    Finsupp.extendDomain_subtypeDomain (ν' : Nat.Primes →₀ ℕ)
      (fun p hp => Finset.coe_subset.mpr ν'.2 hp)
  rw [← occupationRecip_extendDomain_pow r (occupationSupportedEquiv S ν'), hext,
    occupationFactor]
  ring


theorem summable_norm_occupationFactor {r : ℕ} (hr : 2 ≤ r) (x : ℂ) :
    Summable (fun ν : Nat.Primes →₀ ℕ => ‖occupationFactor r x ν‖) := by
  have hbase := (summable_norm_occupationRecip_pow hr).mul_left ‖x‖
  refine hbase.congr fun ν => ?_
  rw [occupationFactor, norm_neg, norm_mul]

/-- The packet-restricted occupation factor, extended by one outside the packet. -/
def packetFactor (r : ℕ) (x : ℂ) (S : Finset Nat.Primes) (ν : Nat.Primes →₀ ℕ) : ℂ :=
  if ν.support ⊆ S then occupationFactor r x ν else 0

theorem norm_packetFactor_le (r : ℕ) (x : ℂ) (S : Finset Nat.Primes) (ν : Nat.Primes →₀ ℕ) :
    ‖packetFactor r x S ν‖ ≤ ‖occupationFactor r x ν‖ := by
  rw [packetFactor]
  by_cases h : ν.support ⊆ S
  · rw [if_pos h]
  · rw [if_neg h, norm_zero]
    exact norm_nonneg _

theorem summable_norm_packetFactor {r : ℕ} (hr : 2 ≤ r) (x : ℂ) (S : Finset Nat.Primes) :
    Summable (fun ν : Nat.Primes →₀ ℕ => ‖packetFactor r x S ν‖) :=
  (summable_norm_occupationFactor hr x).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun ν => norm_packetFactor_le r x S ν)

theorem tprod_packetFactor {r : ℕ} (hr : 2 ≤ r) (x : ℂ) (S : Finset Nat.Primes) :
    ∏' ν : Nat.Primes →₀ ℕ, (1 + packetFactor r x S ν)
      = ∏' ν : ↥(occupationSupported S), (1 + occupationFactor r x (ν : Nat.Primes →₀ ℕ)) := by
  classical
  have hmul := multipliable_one_add_of_summable (summable_norm_packetFactor hr x S)
  have hinj : Function.Injective
      (fun ν : ↥(occupationSupported S) => (ν : Nat.Primes →₀ ℕ)) := Subtype.val_injective
  have hout : ∀ ν ∉ Set.range (fun ν : ↥(occupationSupported S) => (ν : Nat.Primes →₀ ℕ)),
      (1 : ℂ) + packetFactor r x S ν = 1 := by
    intro ν hν
    have hns : ¬ ν.support ⊆ S := fun h => hν ⟨⟨ν, h⟩, rfl⟩
    rw [packetFactor, if_neg hns, add_zero]
  have hsub := (hinj.hasProd_iff hout).mpr hmul.hasProd
  have hcongr : HasProd (fun ν : ↥(occupationSupported S) =>
      1 + occupationFactor r x (ν : Nat.Primes →₀ ℕ))
      (∏' ν : Nat.Primes →₀ ℕ, (1 + packetFactor r x S ν)) := by
    refine hsub.congr_fun fun ν => ?_
    simp only [Function.comp_apply, packetFactor]
    rw [if_pos (show (ν : Nat.Primes →₀ ℕ).support ⊆ S from ν.2)]
  exact hcongr.tprod_eq.symm

/-- **Cofinal completion of the occupation product.**  As the prime packet exhausts the primes, the
packet product converges to the completed product. -/
theorem tendsto_primeOccupationFacePow {r : ℕ} (hr : 2 ≤ r) (x : ℂ) :
    Tendsto (fun S : Finset Nat.Primes => primeOccupationFacePow r S x) atTop
      (𝓝 (HTGeometry.occupationProduct r x)) := by
  classical
  set w : (Nat.Primes →₀ ℕ) → ℝ := fun ν => ‖occupationFactor r x ν‖ with hwdef
  have hw : Summable w := summable_norm_occupationFactor hr x
  set M : ℝ := ∑' ν, w ν with hMdef
  have hfull : HTGeometry.occupationProduct r x
      = ∏' ν : Nat.Primes →₀ ℕ, (1 + occupationFactor r x ν) :=
    (hasProd_occupationProduct_occ hr x).tprod_eq.symm
  have hkey : ∀ S : Finset Nat.Primes,
      ‖HTGeometry.occupationProduct r x - primeOccupationFacePow r S x‖
        ≤ (∑' ν, ‖occupationFactor r x ν - packetFactor r x S ν‖) * Real.exp (2 * M) := by
    intro S
    have hb := GaloisForLFunctions.HTGeometry.norm_tprod_one_add_sub_tprod_one_add_le
      (occupationFactor r x) (packetFactor r x S) (summable_norm_occupationFactor hr x)
      (summable_norm_packetFactor hr x S)
    rw [← hfull, tprod_packetFactor hr x S, ← primeOccupationFacePow_eq_tprod_occ] at hb
    refine hb.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (tsum_nonneg fun ν => norm_nonneg _)
    refine Real.exp_le_exp.mpr ?_
    have hsum : ∑' ν, (‖occupationFactor r x ν‖ + ‖packetFactor r x S ν‖) ≤ ∑' ν, (2 * w ν) := by
      refine Summable.tsum_le_tsum (fun ν => ?_) ((summable_norm_occupationFactor hr x).add
        (summable_norm_packetFactor hr x S)) (hw.mul_left 2)
      have hle := norm_packetFactor_le r x S ν
      rw [hwdef]
      linarith
    rw [tsum_mul_left] at hsum
    rw [hMdef]
    linarith
  have hdiff : ∀ S : Finset Nat.Primes,
      ∑' ν, ‖occupationFactor r x ν - packetFactor r x S ν‖
        = ∑' ν, w ν - ∑' ν : ↥(occupationSupported S), w (ν : Nat.Primes →₀ ℕ) := by
    intro S
    have hpt : ∀ ν, ‖occupationFactor r x ν - packetFactor r x S ν‖
        = (occupationSupported S)ᶜ.indicator w ν := by
      intro ν
      by_cases h : ν.support ⊆ S
      · rw [packetFactor, if_pos h, sub_self, norm_zero,
          Set.indicator_of_notMem
            (show ν ∉ (occupationSupported S)ᶜ from
              fun hc => hc (show ν ∈ occupationSupported S from h))]
      · rw [packetFactor, if_neg h, sub_zero,
          Set.indicator_of_mem (show ν ∈ (occupationSupported S)ᶜ from h), hwdef]
    rw [tsum_congr hpt, ← tsum_subtype]
    have hsplit : (∑' ν : ↥(occupationSupported S), w (ν : Nat.Primes →₀ ℕ))
        + (∑' ν : ↥((occupationSupported S)ᶜ), w (ν : Nat.Primes →₀ ℕ)) = ∑' ν, w ν :=
      Summable.tsum_add_tsum_compl (hw.subtype _) (hw.subtype _)
    linarith
  have hmass : Tendsto (fun S : Finset Nat.Primes =>
      ∑' ν : ↥(occupationSupported S), w (ν : Nat.Primes →₀ ℕ)) atTop (𝓝 (∑' ν, w ν)) := by
    have hsc : Summable (fun ν : Nat.Primes →₀ ℕ => ‖((w ν : ℝ) : ℂ)‖) := by
      refine hw.congr fun ν => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hC := HTGeometry.tendsto_tsum_subtype_of_cofinal
      (f := fun ν : Nat.Primes →₀ ℕ => ((w ν : ℝ) : ℂ)) hsc cofinal_occupationSupported
    have hre := (Complex.continuous_re.tendsto _).comp hC
    have hlim : (∑' i : (Nat.Primes →₀ ℕ), ((w i : ℝ) : ℂ)).re = ∑' i, w i := by
      rw [← Complex.ofReal_tsum, Complex.ofReal_re]
    rw [hlim] at hre
    refine hre.congr fun S => ?_
    rw [Function.comp_apply, ← Complex.ofReal_tsum, Complex.ofReal_re]
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  have hEpos : (0 : ℝ) < Real.exp (2 * M) := Real.exp_pos _
  obtain ⟨S₀, hS₀⟩ := Metric.tendsto_atTop.mp hmass (ε / Real.exp (2 * M)) (by positivity)
  refine ⟨S₀, fun S hS => ?_⟩
  have h1 := hS₀ S hS
  have h2 := hkey S
  rw [hdiff S] at h2
  have h3 : ∑' ν, w ν - ∑' ν : ↥(occupationSupported S), w (ν : Nat.Primes →₀ ℕ)
      < ε / Real.exp (2 * M) := by
    rw [Real.dist_eq] at h1
    have := abs_lt.mp h1
    linarith [this.1, this.2]
  rw [Complex.dist_eq]
  calc ‖primeOccupationFacePow r S x - HTGeometry.occupationProduct r x‖
      = ‖HTGeometry.occupationProduct r x - primeOccupationFacePow r S x‖ := norm_sub_rev _ _
    _ ≤ (∑' ν, w ν - ∑' ν : ↥(occupationSupported S), w (ν : Nat.Primes →₀ ℕ))
        * Real.exp (2 * M) := h2
    _ < (ε / Real.exp (2 * M)) * Real.exp (2 * M) := mul_lt_mul_of_pos_right h3 hEpos
    _ = ε := by field_simp


/-! ## The Euler boundary jet in the occupation indexing -/

theorem occupationRecip_pow_eq (k : ℕ) (ν : Nat.Primes →₀ ℕ) :
    occupationRecip ν ^ k = HTGeometry.natPowInvHom k (primeProduct ν) := by
  rw [occupationRecip_eq, HTGeometry.natPowInvHom_apply, inv_pow]

/-- **The completed occupation power sum is a zeta value.**  Unique factorization turns the sum of
`n^{-k}` over all occupation vectors into the Dirichlet series of the Riemann zeta function. -/
theorem tsum_occupationRecip_pow_eq_riemannZeta {k : ℕ} (hk : 2 ≤ k) :
    ∑' ν : Nat.Primes →₀ ℕ, occupationRecip ν ^ k = riemannZeta (k : ℂ) := by
  have hzero : ∀ n ∉ Set.range (fun m : {m : ℕ // m ≠ 0} => (m : ℕ)),
      HTGeometry.natPowInvHom k n = 0 := by
    intro n hn
    have hn0 : n = 0 := by
      by_contra h
      exact hn ⟨⟨n, h⟩, rfl⟩
    rw [hn0, HTGeometry.natPowInvHom_apply, Nat.cast_zero, zero_pow (by omega : k ≠ 0), inv_zero]
  have hsumℕ := (HTGeometry.summable_natPowInvHom hk).hasSum
  have hsub : HasSum (fun m : {m : ℕ // m ≠ 0} => HTGeometry.natPowInvHom k (m : ℕ))
      (∑' n : ℕ, HTGeometry.natPowInvHom k n) :=
    (Subtype.val_injective.hasSum_iff hzero).mpr hsumℕ
  have hocc := (occupationEquivNatPos.hasSum_iff
    (f := fun m : {m : ℕ // m ≠ 0} => HTGeometry.natPowInvHom k (m : ℕ))).mpr hsub
  have hfin : HasSum (fun ν : Nat.Primes →₀ ℕ => occupationRecip ν ^ k)
      (∑' n : ℕ, HTGeometry.natPowInvHom k n) := by
    refine hocc.congr_fun fun ν => ?_
    simp only [Function.comp_apply]
    rw [occupationRecip_pow_eq]
    rfl
  rw [hfin.tsum_eq]
  exact HTGeometry.tsum_natPowInvHom_eq_riemannZeta hk

/-- **The Euler boundary jet.**  Every occupation power sum of a finite prime packet converges
cofinally to the corresponding zeta value. -/
theorem tendsto_smoothPowerSum_riemannZeta {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun S : Finset Nat.Primes => smoothPowerSum S k) atTop
      (𝓝 (riemannZeta (k : ℂ))) := by
  rw [← tsum_occupationRecip_pow_eq_riemannZeta hk]
  exact tendsto_smoothPowerSum hk

/-! ## The finite Euler factorization of a packet power sum -/

theorem nomeMonomial_primePowerNome (k : ℕ) (ν : Nat.Primes →₀ ℕ) :
    HTGeometry.nomeMonomial (fun p : Nat.Primes => primePowerNome k p) ν
      = occupationRecip ν ^ k := by
  classical
  rw [occupationRecip, HTGeometry.nomeMonomial, HTGeometry.nomeMonomial, Finsupp.prod,
    Finsupp.prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [primePowerNome, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **The Euler factorization of a packet power sum.**  The occupation power sum of a finite prime
packet is the finite Euler product over its primes. -/
theorem smoothPowerSum_eq_prod {k : ℕ} (hk : 1 ≤ k) (S : Finset Nat.Primes) :
    smoothPowerSum S k = ∏ p ∈ S, (1 - primePowerNome k p)⁻¹ := by
  have hu : ∀ p : Nat.Primes, ‖primePowerNome k p‖ < 1 := fun p =>
    norm_primePowerNome_lt_one hk p
  have h := HTGeometry.hasSum_supported_nomeMonomial
    (fun p : Nat.Primes => primePowerNome k p) hu S
  have hcongr : HasSum
      (fun ν : ↥(occupationSupported S) => occupationRecip (ν : Nat.Primes →₀ ℕ) ^ k)
      (∏ p ∈ S, (1 - primePowerNome k p)⁻¹) := by
    refine h.congr_fun fun ν => ?_
    exact (nomeMonomial_primePowerNome k (ν : Nat.Primes →₀ ℕ)).symm
  exact hcongr.tsum_eq

/-- **The Euler boundary jet, in Euler-product form.**  The finite Euler product of a packet
converges cofinally to the zeta value. -/
theorem tendsto_prod_primePowerNome_riemannZeta {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - primePowerNome k p)⁻¹) atTop
      (𝓝 (riemannZeta (k : ℂ))) := by
  refine (tendsto_smoothPowerSum_riemannZeta hk).congr fun S => ?_
  exact smoothPowerSum_eq_prod (by omega) S

/-! ## The first Euler coefficient of a packet -/

/-- **The derivative at the origin of a packet product.**  The first logarithmic coefficient of the
occupation product of a finite prime packet is minus its occupation power sum. -/
theorem hasDerivAt_primeOccupationFacePow_zero {r : ℕ} (hr : 2 ≤ r) (S : Finset Nat.Primes) :
    HasDerivAt (primeOccupationFacePow r S) (-smoothPowerSum S r) 0 := by
  classical
  have hqs : Summable (fun ν : ↥(occupationSupported S) =>
      ‖-(occupationRecip (ν : Nat.Primes →₀ ℕ) ^ r)‖) := by
    refine ((summable_norm_occupationRecip_pow hr).subtype (occupationSupported S)).congr
      fun ν => ?_
    rw [norm_neg]
  have hd := GaloisForLFunctions.HTGeometry.hasDerivAt_tprod_one_add_mul hqs
  have hfun : (fun x : ℂ => ∏' ν : ↥(occupationSupported S),
      (1 + x * -(occupationRecip (ν : Nat.Primes →₀ ℕ) ^ r)))
      = primeOccupationFacePow r S := by
    funext x
    rw [primeOccupationFacePow_eq_tprod_occ]
    refine tprod_congr fun ν => ?_
    rw [occupationFactor]
    ring
  have hval : (∑' ν : ↥(occupationSupported S),
      -(occupationRecip (ν : Nat.Primes →₀ ℕ) ^ r)) = -smoothPowerSum S r := by
    rw [smoothPowerSum, ← tsum_neg]
  rw [hfun, hval] at hd
  exact hd

theorem deriv_primeOccupationFacePow_zero {r : ℕ} (hr : 2 ≤ r) (S : Finset Nat.Primes) :
    deriv (primeOccupationFacePow r S) 0 = -smoothPowerSum S r :=
  (hasDerivAt_primeOccupationFacePow_zero hr S).deriv

/-- **The first Euler coefficient converges to the zeta value.**  This is the packet form of the
completion statement `Φ'_{S,r}(0) → -ζ(r)`. -/
theorem tendsto_deriv_primeOccupationFacePow_zero {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun S : Finset Nat.Primes => deriv (primeOccupationFacePow r S) 0) atTop
      (𝓝 (-riemannZeta (r : ℂ))) := by
  have h := (tendsto_smoothPowerSum_riemannZeta hr).neg
  refine h.congr fun S => ?_
  exact (deriv_primeOccupationFacePow_zero hr S).symm

end

end GaloisForLFunctions
