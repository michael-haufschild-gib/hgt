import GaloisForLFunctions.RHTower.XiRealAxisGrowth
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.RHTower.XiRightHalfSquareRootBoundaryNoExtension
import GaloisForLFunctions.HTGeometry.MeromorphicPlaneSquareRoot

/-!
# Independent global square classes from the completed Xi function

For every nonempty finite set of distinct integers `n ≥ 2`, every product of the factors
`1 - exp(-s log n) * xi(s)`, times any nonnegative power of Xi, is nonsquare in the field of
meromorphic functions on the entire complex plane. A real crossing between the least label
and the next integer gives a strict sign change. Schwarz reflection excludes a global square.
The remaining class of Xi is nonsquare by its existing odd-order-zero theorem.
-/

open Complex Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower.XiGlobalKummer

/-- Xi takes real values on the real axis. -/
theorem xi_real_cast (t : ℝ) : ((xi (t : ℂ)).re : ℂ) = xi t := by
  have h := congrArg Complex.im (xi_conj (t : ℂ))
  simp only [conj_ofReal, conj_im] at h
  apply Complex.ext
  · simp
  · simp only [ofReal_im]
    linarith

/-- Xi is strictly positive on the whole real axis. -/
theorem xi_real_pos (t : ℝ) : 0 < (xi (t : ℂ)).re := by
  by_contra! h
  have hc : Continuous (fun t : ℝ => (xi (t : ℂ)).re) :=
    Complex.continuous_re.comp (xi_differentiable.continuous.comp Complex.continuous_ofReal)
  have h1 : (xi (1 : ℂ)).re = 1 / 2 := by rw [xi_one]; norm_num
  obtain ⟨u, hu⟩ := intermediate_value_univ t 1 hc
    (show (0 : ℝ) ∈ Set.Icc (xi (t : ℂ)).re (xi (1 : ℂ)).re from ⟨h, by rw [h1]; norm_num⟩)
  apply xi_ne_zero_of_real u
  change (xi (u : ℂ)).re = 0 at hu
  rw [← xi_real_cast u, hu]
  simp

/-- The norm of Xi on the real axis equals its positive real part. -/
theorem xi_real_norm (t : ℝ) : ‖xi (t : ℂ)‖ = (xi (t : ℂ)).re := by
  conv_lhs => rw [← xi_real_cast t]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (xi_real_pos t)]

/-- Xi exceeds every fixed exponential rate somewhere to the right of one. -/
theorem exists_xi_real_above_exp (c : ℝ) :
    ∃ t : ℝ, 1 < t ∧ Real.exp (c * t) < (xi (t : ℂ)).re := by
  obtain ⟨m, hm⟩ := (eventually_lt_log_norm_xi c).exists
  refine ⟨2 * ((m : ℝ) + 1), by have hm0 := Nat.cast_nonneg (α := ℝ) m; linarith, ?_⟩
  have hcast : ((2 * ((m : ℝ) + 1) : ℝ) : ℂ) = 2 * ((m : ℂ) + 1) := by push_cast; rfl
  rw [← hcast, xi_real_norm] at hm
  exact (Real.lt_log_iff_exp_lt (xi_real_pos _)).mp hm

/-- Every positive exponential rate crosses Xi to the right of one. -/
theorem exists_xi_real_exp_crossing {c : ℝ} (hc : 0 < c) :
    ∃ t : ℝ, 1 < t ∧ (xi (t : ℂ)).re = Real.exp (c * t) := by
  obtain ⟨b, hb, hexp⟩ := exists_xi_real_above_exp c
  let f : ℝ → ℝ := fun t => (xi (t : ℂ)).re - Real.exp (c * t)
  have hfc : Continuous f :=
    (Complex.continuous_re.comp (xi_differentiable.continuous.comp Complex.continuous_ofReal)).sub
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hf1 : f 1 < 0 := by
    have h := Real.one_lt_exp_iff.mpr hc
    dsimp [f]
    rw [xi_one]
    norm_num at ⊢
    linarith
  have hfb : 0 < f b := sub_pos.mpr hexp
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hb.le hfc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f 1) (f b) from ⟨hf1.le, hfb.le⟩)
  refine ⟨t, lt_of_le_of_ne ht.1 ?_, sub_eq_zero.mp hft⟩
  intro he
  subst t
  linarith


/-- The entire factor whose global square class records the marked source cover. -/
def deletionFactor (n : ℕ) (s : ℂ) : ℂ :=
  1 - Complex.exp (-s * (Real.log n : ℂ)) * xi s

/-- The real restriction of the marked source factor. -/
def realFactor (n : ℕ) (t : ℝ) : ℝ :=
  1 - Real.exp (-t * Real.log n) * (xi (t : ℂ)).re

/-- A finite product of marked source factors, with an additional Xi power. -/
def packet (S : Finset ℕ) (e : ℕ) (s : ℂ) : ℂ :=
  xi s ^ e * ∏ n ∈ S, deletionFactor n s

/-- The real restriction of a finite marked source packet. -/
def realPacket (S : Finset ℕ) (e : ℕ) (t : ℝ) : ℝ :=
  (xi (t : ℂ)).re ^ e * ∏ n ∈ S, realFactor n t

theorem deletionFactor_differentiable (n : ℕ) : Differentiable ℂ (deletionFactor n) := by
  exact (differentiable_const (c := (1 : ℂ))).sub
    (((differentiable_id.neg.mul_const (Real.log n : ℂ)).cexp).mul xi_differentiable)

theorem packet_differentiable (S : Finset ℕ) (e : ℕ) : Differentiable ℂ (packet S e) := by
  have hp : Differentiable ℂ (fun s => ∏ n ∈ S, deletionFactor n s) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert n S hn ih =>
      simp_rw [Finset.prod_insert hn]
      exact (deletionFactor_differentiable n).mul ih
  exact (xi_differentiable.pow e).mul hp

theorem realFactor_cast (n : ℕ) (t : ℝ) : (realFactor n t : ℂ) = deletionFactor n t := by
  simp only [realFactor, deletionFactor, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg, xi_real_cast]

theorem realPacket_cast (S : Finset ℕ) (e : ℕ) (t : ℝ) :
    (realPacket S e t : ℂ) = packet S e t := by
  simp only [realPacket, packet, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_prod,
    xi_real_cast, realFactor_cast]

theorem deletionFactor_conj (n : ℕ) (s : ℂ) :
    deletionFactor n (conj s) = conj (deletionFactor n s) := by
  simp only [deletionFactor, map_sub, map_one, map_mul, map_neg, conj_ofReal,
    xi_conj, ← Complex.exp_conj]

theorem packet_conj (S : Finset ℕ) (e : ℕ) (s : ℂ) :
    packet S e (conj s) = conj (packet S e s) := by
  simp only [packet, map_mul, map_pow, map_prod, xi_conj, deletionFactor_conj]

/-- Every integer-labelled factor with label at least two is positive at one. -/
theorem realFactor_one_pos {n : ℕ} (hn : 2 ≤ n) : 0 < realFactor n 1 := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have he := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.log_pos hn1))
  have hxi : (xi (1 : ℂ)).re = 1 / 2 := by rw [xi_one]; norm_num
  simp only [realFactor, Complex.ofReal_one, hxi, neg_mul, one_mul]
  linarith

/-- Every admissible packet is positive at one. -/
theorem realPacket_one_pos (S : Finset ℕ) (e : ℕ) (hS : ∀ n ∈ S, 2 ≤ n) :
    0 < realPacket S e 1 := by
  exact mul_pos (pow_pos (xi_real_pos 1) e)
    (Finset.prod_pos fun n hn => realFactor_one_pos (hS n hn))

theorem realFactor_at_crossing (n : ℕ) {c t : ℝ}
    (hcross : (xi (t : ℂ)).re = Real.exp (c * t)) :
    realFactor n t = 1 - Real.exp ((c - Real.log n) * t) := by
  rw [realFactor, hcross, ← Real.exp_add]
  congr 2
  ring

/-- An exponential crossing makes exactly the least-labelled factor negative. -/
theorem exists_realPacket_neg (S : Finset ℕ) (e : ℕ)
    (hne : S.Nonempty) (hS : ∀ n ∈ S, 2 ≤ n) :
    ∃ t : ℝ, 1 < t ∧ realPacket S e t < 0 := by
  let p := S.min' hne
  have hpS : p ∈ S := S.min'_mem hne
  have hp2 := hS p hpS
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  have hlog : Real.log (p : ℝ) < Real.log ((p : ℝ) + 1) :=
    Real.log_lt_log hp0 (by linarith)
  let c := (Real.log (p : ℝ) + Real.log ((p : ℝ) + 1)) / 2
  have hpc : Real.log (p : ℝ) < c := by dsimp [c]; linarith
  have hcp : c < Real.log ((p : ℝ) + 1) := by dsimp [c]; linarith
  have hc : 0 < c := lt_trans (Real.log_pos hp1) hpc
  obtain ⟨t, ht, hcross⟩ := exists_xi_real_exp_crossing hc
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hneg : realFactor p t < 0 := by
    rw [realFactor_at_crossing p hcross, sub_neg]
    exact Real.one_lt_exp_iff.mpr (mul_pos (sub_pos.mpr hpc) ht0)
  have hpos : ∀ n ∈ S.erase p, 0 < realFactor n t := by
    intro n hn
    have hpn : p < n := S.min'_lt_of_mem_erase_min' hne hn
    have hpnR : (p : ℝ) + 1 ≤ n := by exact_mod_cast hpn
    have hnlog : Real.log ((p : ℝ) + 1) ≤ Real.log n :=
      Real.log_le_log (by positivity) hpnR
    rw [realFactor_at_crossing n hcross, sub_pos]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith) ht0)
  refine ⟨t, ht, ?_⟩
  unfold realPacket
  rw [← Finset.mul_prod_erase S (fun n => realFactor n t) hpS]
  exact mul_neg_of_pos_of_neg (pow_pos (xi_real_pos t) e)
    (mul_neg_of_neg_of_pos hneg (Finset.prod_pos hpos))


open GaloisForLFunctions.HTGeometry

/-- Xi as an element of the field of globally meromorphic plane functions. -/
def xiElement : MeromorphicPlane :=
  ofMeromorphic xi (fun z => (xi_differentiable.analyticAt z).meromorphicAt)

/-- The marked source factor in the global meromorphic plane field. -/
def factorElement (n : ℕ) : MeromorphicPlane :=
  ofMeromorphic (deletionFactor n)
    (fun z => ((deletionFactor_differentiable n).analyticAt z).meromorphicAt)

/-- The entire finite packet in the global meromorphic plane field. -/
def packetElement (S : Finset ℕ) (e : ℕ) : MeromorphicPlane :=
  ofMeromorphic (packet S e)
    (fun z => ((packet_differentiable S e).analyticAt z).meromorphicAt)

private def planeGermHom : MeromorphicPlane →+* Germ planeCodiscrete ℂ where
  toFun := MeromorphicPlane.germ
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The analytic packet agrees with the product in the global meromorphic field. -/
theorem packetElement_eq (S : Finset ℕ) (e : ℕ) :
    packetElement S e = xiElement ^ e * ∏ n ∈ S, factorElement n := by
  apply MeromorphicPlane.germ_injective
  change Germ.coeRingHom planeCodiscrete (packet S e) =
    planeGermHom (xiElement ^ e * ∏ n ∈ S, factorElement n)
  have hp : packet S e = xi ^ e * ∏ n ∈ S, deletionFactor n := by
    ext z
    simp [packet]
  rw [hp, map_mul, map_pow, map_prod, map_mul, map_pow, map_prod]
  rfl

/-- Every nonempty admissible packet is globally nonsquare. -/
theorem packetElement_not_isSquare (S : Finset ℕ) (e : ℕ)
    (hne : S.Nonempty) (hS : ∀ n ∈ S, 2 ≤ n) :
    ¬ IsSquare (packetElement S e) := by
  obtain ⟨t, _, ht⟩ := exists_realPacket_neg S e hne hS
  apply not_isSquare_plane_of_real_sign_change (packet_differentiable S e) (packet_conj S e)
    (x := 1) (y := t)
  have hx := realPacket_one_pos S e hS
  have h1 : (packet S e ((1 : ℝ) : ℂ)).re = realPacket S e 1 := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re (realPacket_cast S e 1).symm
  have h2 : (packet S e (t : ℂ)).re = realPacket S e t := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re (realPacket_cast S e t).symm
  rw [h1, h2]
  exact mul_neg_of_pos_of_neg hx ht

/-- No finite nonempty factor product becomes a square after any Xi power twist. -/
theorem xi_pow_mul_prod_factors_not_isSquare (S : Finset ℕ) (e : ℕ)
    (hne : S.Nonempty) (hS : ∀ n ∈ S, 2 ≤ n) :
    ¬ IsSquare (xiElement ^ e * ∏ n ∈ S, factorElement n) := by
  rw [← packetElement_eq]
  exact packetElement_not_isSquare S e hne hS

/-- Xi itself has no square root in the global meromorphic plane field. -/
theorem xiElement_not_isSquare : ¬ IsSquare xiElement := by
  intro h
  exact not_exists_entire_sqrt_xi (entire_sqrt_of_isSquare_plane xi_differentiable h)

theorem xiElement_ne_zero : xiElement ≠ 0 := by
  intro h
  exact xiElement_not_isSquare (h ▸ IsSquare.zero)

/-- Each individual marked source factor is globally nonsquare. -/
theorem factorElement_not_isSquare {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsSquare (factorElement n) := by
  simpa using xi_pow_mul_prod_factors_not_isSquare {n} 0 (by simp)
    (by simpa using hn)

theorem factorElement_ne_zero {n : ℕ} (hn : 2 ≤ n) : factorElement n ≠ 0 := by
  intro h
  exact factorElement_not_isSquare hn (h ▸ IsSquare.zero)

end RHTower.XiGlobalKummer