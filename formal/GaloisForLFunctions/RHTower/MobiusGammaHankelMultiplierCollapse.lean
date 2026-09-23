import GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelWall
import GaloisForLFunctions.HTGeometry.BurnolDepthCompletion
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
Möbius coefficient multiplication is unbounded in every positive-order
Gamma--Hankel energy. The source Hilbert norm and additive completion norm
cannot be interchanged when interpreting Möbius coefficients as a grading.

Paper proof: for 0<p<=q and x>0,
0 <= exp(-px)-exp(-qx) <= (q-p)x exp(-px).
Its weighted square integral is at most
(q-p)^(2 : ℕ) Gamma(r+2)/(2p)^(r+2). At a prime p and a multiple
of four q in (p,p+4], multiplication by mu sends this difference
to -exp(-px), whose energy is Gamma(r)/(2p)^r. Their ratio
exceeds any fixed constant as p grows.

Stronger completion law: the atoms x^((r-1)/2) exp(-4(k+1)x)
span densely in L2(0,infinity). Orthogonality gives vanishing integer
Laplace moments of an L1 density; the existing moment determinacy
theorem forces that density to vanish. All these atoms are killed by
mu. The closure of any proposed multiplier graph therefore contains
the whole horizontal axis as well as (v_1,v_1), hence (0,v_1) with
v_1 nonzero. It cannot be a graph, even of an unbounded operator.
The finite sum norm is proved equal to the corpus Gamma--Hankel energy.

Positive survivors: quantitative dipole estimate and squareful-atom
totality. This is a kernel/observable compatibility bridge, not a proof
of RH or a no-go for actual Mobius-prefix returns. It does not exclude
coefficient-space grading or synthesis between distinct completions.
-/

open MeasureTheory Set
open Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section

/-- Two unit integer-frequency atoms with opposite coefficients. -/
def gammaHankelDipole (i j : ℕ) (n : ℕ) : ℝ :=
  (if n = i then 1 else 0) - (if n = j then 1 else 0)

theorem finiteRealLaplacePencil_dipole {i j N : ℕ}
    (hi : i < N) (hj : j < N) (x : ℝ) :
    finiteRealLaplacePencil (gammaHankelDipole i j) N x =
      Real.exp (-((i+1:ℕ):ℝ)*x) - Real.exp (-((j+1:ℕ):ℝ)*x) := by
  classical
  simp [finiteRealLaplacePencil, gammaHankelDipole, sub_mul,
    Finset.sum_sub_distrib, ite_mul, hi, hj]

private theorem laplace_dipole_pointwise {p q x : ℝ}
    (hpq : p ≤ q) (hx : 0 ≤ x) :
    (Real.exp (-p*x) - Real.exp (-q*x))^(2 : ℕ) ≤
      (q-p)^(2 : ℕ)*x^(2 : ℕ)*Real.exp (-(2*p)*x) := by
  have he : Real.exp (-q*x) = Real.exp (-p*x)*Real.exp (-(q-p)*x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hz : 0 ≤ (q-p)*x := mul_nonneg (sub_nonneg.mpr hpq) hx
  have hlo : 0 ≤ 1-Real.exp (-(q-p)*x) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hhi : 1-Real.exp (-(q-p)*x) ≤ (q-p)*x := by
    have h := Real.add_one_le_exp (-(q-p)*x)
    linarith
  have hsq : (1-Real.exp (-(q-p)*x))^(2 : ℕ) ≤ ((q-p)*x)^(2 : ℕ) :=
    (sq_le_sq₀ hlo hz).mpr hhi
  have he2 : Real.exp (-p*x)^(2 : ℕ) = Real.exp (-(2*p)*x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  calc
    _ = Real.exp (-p*x)^(2 : ℕ) * (1-Real.exp (-(q-p)*x))^(2 : ℕ) := by ring
    _ ≤ Real.exp (-p*x)^(2 : ℕ) * ((q-p)*x)^(2 : ℕ) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by rw [he2]; ring

/-- Nearby Laplace atoms have quadratically small difference energy. -/
theorem gammaHankelDipole_energy_le {i j N : ℕ}
    (hi : i < N) (hj : j < N) (hij : i ≤ j) {r : ℝ} (hr : 0 < r) :
    finiteGammaHankelEnergy (gammaHankelDipole i j) N r ≤
      (((j+1:ℕ):ℝ)-((i+1:ℕ):ℝ))^(2 : ℕ) * Real.Gamma (r+2) /
        (2*((i+1:ℕ):ℝ))^(r+2) := by
  let p : ℝ := i+1
  let q : ℝ := j+1
  have hp : 0 < p := by dsimp [p]; positivity
  have hpq : p ≤ q := by dsimp [p,q]; exact_mod_cast Nat.add_le_add_right hij 1
  have hb : 0 < 2*p := by positivity
  have hint : IntegrableOn (fun x : ℝ => x^(r+1)*Real.exp (-(2*p)*x)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ))
        (s := r+1) (b := 2*p) (by linarith) (by norm_num) hb)
  have heval : (∫ x : ℝ in Ioi 0, x^(r+1)*Real.exp (-(2*p)*x)) =
      Real.Gamma (r+2)/(2*p)^(r+2) := by
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ))
      (q := r+1) (b := 2*p) (by norm_num) (by linarith) hb
    simp only [Real.rpow_one, div_one, mul_one] at h
    rw [show r+1+1=r+2 by ring, Real.rpow_neg hb.le] at h
    simpa [div_eq_mul_inv, mul_comm] using h
  rw [← integral_finiteRealLaplacePencil_sq _ _ hr]
  calc
    _ ≤ ∫ x : ℝ in Ioi 0, (q-p)^(2 : ℕ)*(x^(r+1)*Real.exp (-(2*p)*x)) := by
      apply setIntegral_mono_on (integrableOn_finiteRealLaplacePencil_sq _ _ hr)
        (hint.const_mul _) measurableSet_Ioi
      intro x hx
      rw [finiteRealLaplacePencil_dipole hi hj]
      simp only [Nat.cast_add, Nat.cast_one]
      change x^(r-1)*(Real.exp (-p*x)-Real.exp (-q*x))^(2 : ℕ) ≤
        (q-p)^(2 : ℕ)*(x^(r+1)*Real.exp (-(2*p)*x))
      have hbound := mul_le_mul_of_nonneg_left (laplace_dipole_pointwise hpq hx.le)
        (Real.rpow_nonneg hx.le (r-1))
      have hpow : x^(r-1)*x^(2 : ℕ) = x^(r+1) := by
        rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx]
        congr 1
        ring
      calc
        _ ≤ x^(r-1)*((q-p)^(2 : ℕ)*x^(2 : ℕ)*Real.exp (-(2*p)*x)) := hbound
        _ = _ := by rw [← hpow]; ring
    _ = _ := by rw [integral_const_mul, heval]; dsimp [p,q]; push_cast; ring

private theorem finiteGammaHankelEnergy_single {i N : ℕ} (hi : i < N) (a r : ℝ) :
    finiteGammaHankelEnergy (fun n => if n=i then a else 0) N r =
      Real.Gamma r*a^(2 : ℕ)/(2*((i+1:ℕ):ℝ))^r := by
  classical
  simp [finiteGammaHankelEnergy, ite_mul, mul_ite, ite_div, hi]
  ring

private theorem mobius_four_mul_zero (k : ℕ) :
    ArithmeticFunction.moebius (4*k) = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsq
  have hd : 2*2 ∣ 4*k := ⟨k, by ring⟩
  have hunit := hsq 2 hd
  exact (by norm_num : ¬ IsUnit (2:ℕ)) hunit

/-- No cutoff-independent bound transports coefficientwise Möbius multiplication
to the additive Gamma--Hankel norm, at any positive exponent. -/
theorem not_mobius_gammaHankel_multiplier_bounded {r : ℝ} (hr : 0 < r) :
    ¬ ∃ C : ℝ, ∀ (a : ℕ → ℝ) (N : ℕ),
      finiteGammaHankelEnergy (fun n => shiftedMobiusRealCoefficient n*a n) N r ≤
        C*finiteGammaHankelEnergy a N r := by
  rintro ⟨C, hC⟩
  have hg : 0 < Real.Gamma r := Real.Gamma_pos_of_pos hr
  have hg2 : 0 < Real.Gamma (r+2) := Real.Gamma_pos_of_pos (by linarith)
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hCB : C ≤ B := le_max_left _ _
  obtain ⟨K, hK⟩ := exists_nat_gt (4*B*Real.Gamma (r+2)/Real.Gamma r+1)
  obtain ⟨p, hKp, hpprime⟩ := Nat.exists_infinite_primes K
  let q := 4*(p/4+1)
  have hp : 0 < p := hpprime.pos
  have hpq : p < q := by dsimp [q]; omega
  have hq : q ≤ p+4 := by dsimp [q]; omega
  have hpr : 0 < (p:ℝ) := by exact_mod_cast hp
  have hpr1 : 1 ≤ (p:ℝ) := by exact_mod_cast hpprime.one_lt.le
  have hdiff : 0 ≤ (q:ℝ)-(p:ℝ) := sub_nonneg.mpr (by exact_mod_cast hpq.le)
  have hdiff4 : (q:ℝ)-(p:ℝ) ≤ 4 := by
    apply (sub_le_iff_le_add).mpr
    exact_mod_cast (show q ≤ 4+p by omega)
  have hdiffsq : ((q:ℝ)-(p:ℝ))^(2 : ℕ) ≤ 16 := by nlinarith
  have hi : p-1 < q := by omega
  have hj : q-1 < q := by omega
  have hij : p-1 ≤ q-1 := by omega
  have hps : p-1+1=p := by omega
  have hqs : q-1+1=q := by omega
  have hsp : shiftedMobiusRealCoefficient (p-1) = -1 := by
    simp [shiftedMobiusRealCoefficient, hps,
      ArithmeticFunction.moebius_apply_prime hpprime]
  have hsq : shiftedMobiusRealCoefficient (q-1) = 0 := by
    simp only [shiftedMobiusRealCoefficient, hqs]
    rw [show q=4*(p/4+1) by rfl, mobius_four_mul_zero]
    norm_num
  have hout : (fun n => shiftedMobiusRealCoefficient n * gammaHankelDipole (p-1) (q-1) n) =
      (fun n => if n=p-1 then -1 else 0) := by
    funext n
    by_cases hn : n=p-1
    · subst n
      simp [gammaHankelDipole, hsp, show p-1 ≠ q-1 by omega]
    by_cases hnq : n=q-1
    · subst n
      simp [gammaHankelDipole, hsq, hn]
    · simp [gammaHankelDipole, hn, hnq]
  have hbound := hC (gammaHankelDipole (p-1) (q-1)) q
  rw [hout, finiteGammaHankelEnergy_single hi, hps] at hbound
  norm_num only [neg_one_sq, mul_one] at hbound
  have hein := gammaHankelDipole_energy_le hi hj hij hr
  rw [hps,hqs] at hein
  have hd : 0 < (2*(p:ℝ))^r := Real.rpow_pos_of_pos (by positivity) _
  have hd2 : 0 < (2*(p:ℝ))^(r+2) := Real.rpow_pos_of_pos (by positivity) _
  have hbound' : Real.Gamma r/(2*(p:ℝ))^r ≤
      B*(16*Real.Gamma (r+2)/(2*(p:ℝ))^(r+2)) := by
    calc
      _ ≤ C*finiteGammaHankelEnergy (gammaHankelDipole (p-1) (q-1)) q r := hbound
      _ ≤ B*finiteGammaHankelEnergy (gammaHankelDipole (p-1) (q-1)) q r :=
        mul_le_mul_of_nonneg_right hCB (finiteGammaHankelEnergy_nonneg _ _ hr)
      _ ≤ B*(((q:ℝ)-(p:ℝ))^(2 : ℕ)*Real.Gamma (r+2)/(2*(p:ℝ))^(r+2)) :=
        mul_le_mul_of_nonneg_left hein hB
      _ ≤ _ := by gcongr
  have hpow : (2*(p:ℝ))^(r+2) = (2*(p:ℝ))^r*(2*(p:ℝ))^(2 : ℕ) := by
    simpa only [Real.rpow_two] using Real.rpow_add (by positivity : 0 < 2*(p:ℝ)) r 2
  rw [hpow] at hbound'
  have hp2 : 0 < (2*(p:ℝ))^(2 : ℕ) := sq_pos_of_pos (by positivity)
  have hcancel : Real.Gamma r*(2*(p:ℝ))^(2 : ℕ) ≤ 16*B*Real.Gamma (r+2) := by
    rw [← mul_div_assoc] at hbound'
    have hc := (div_le_div_iff₀ hd (mul_pos hd hp2)).mp hbound'
    apply (mul_le_mul_iff_right₀ hd).mp
    convert hc using 1 <;> ring
  have hlarge : 4*B*Real.Gamma (r+2)/Real.Gamma r+1 < (p:ℝ) :=
    hK.trans_le (by exact_mod_cast hKp)
  have hlt : 4*B*Real.Gamma (r+2) < Real.Gamma r*(p:ℝ) := by
    have hh : 4*B*Real.Gamma (r+2)/Real.Gamma r < (p:ℝ) := by linarith
    have hh' := (div_lt_iff₀ hg).mp hh
    nlinarith
  have hpp : (p:ℝ) ≤ (p:ℝ)^(2 : ℕ) := by nlinarith
  have hppg := mul_le_mul_of_nonneg_left hpp hg.le
  nlinarith

/-- The physical half-density of one positive integer-frequency atom. -/
def gammaLaplaceFeature (r : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (x^((r-1)/2)*Real.exp (-((n+1:ℕ):ℝ)*x) : ℝ)

theorem memLp_gammaLaplaceFeature {r : ℝ} (hr : 0 < r) (n : ℕ) :
    MemLp (gammaLaplaceFeature r n) 2 (volume.restrict (Ioi (0:ℝ))) := by
  have hb : 0 < 2*((n+1:ℕ):ℝ) := by positivity
  have hint := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ))
    (s := r-1) (b := 2*((n+1:ℕ):ℝ)) (by linarith) (by norm_num) hb
  apply (memLp_two_iff_integrable_sq_norm
    ((show Measurable (gammaLaplaceFeature r n) by
      unfold gammaLaplaceFeature; fun_prop).aestronglyMeasurable)).mpr
  apply hint.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hpow : (x^((r-1)/2))^(2 : ℕ) = x^(r-1) := by
    rw [← Real.rpow_natCast (x^((r-1)/2)) 2, ← Real.rpow_mul hx.le]
    congr 1
    ring
  simp only [gammaLaplaceFeature, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, Real.rpow_one, mul_pow, hpow]
  rw [pow_two (Real.exp _), ← Real.exp_add]
  congr 2
  ring

/-- Integer atoms embedded in the actual weighted additive completion. -/
def gammaLaplaceAtom (r : Ioi (0:ℝ)) (n : ℕ) : HTGeometry.BurnolHalfLineL2 :=
  (memLp_gammaLaplaceFeature r.property n).toLp (gammaLaplaceFeature r n)

theorem gammaLaplaceAtom_ae (r : Ioi (0:ℝ)) (n : ℕ) :
    (gammaLaplaceAtom r n : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0:ℝ))]
      gammaLaplaceFeature r n := (memLp_gammaLaplaceFeature r.property n).coeFn_toLp

/-- These are exactly the Gamma--Hankel atoms, not an orthogonal coefficient model. -/
theorem inner_gammaLaplaceAtom (r : Ioi (0:ℝ)) (m n : ℕ) :
    inner ℂ (gammaLaplaceAtom r m) (gammaLaplaceAtom r n) =
      ((Real.Gamma r/((m+n+2:ℕ):ℝ)^(r:ℝ) : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have hint : (∫ x in Ioi (0:ℝ),
      x^((r:ℝ)-1)*Real.exp (-((m+n+2:ℕ):ℝ)*x)) =
      Real.Gamma r/((m+n+2:ℕ):ℝ)^(r:ℝ) := by
    have hb : 0 < ((m+n+2:ℕ):ℝ) := by positivity
    have hr : 0 < (r:ℝ) := r.property
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ))
      (q := (r:ℝ)-1) (b := ((m+n+2:ℕ):ℝ)) (by norm_num)
      (by linarith) hb
    simp only [Real.rpow_one, sub_add_cancel, div_one, mul_one,
      Real.rpow_neg hb.le] at h
    simpa [div_eq_mul_inv, mul_comm] using h
  rw [← hint, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [gammaLaplaceAtom_ae r m, gammaLaplaceAtom_ae r n,
    ae_restrict_mem measurableSet_Ioi] with x hm hn hx
  rw [hm,hn,RCLike.inner_apply]
  simp only [gammaLaplaceFeature, Complex.conj_ofReal, ← Complex.ofReal_mul]
  congr 1
  have hpow : (x^(((r:ℝ)-1)/2))^(2 : ℕ) = x^((r:ℝ)-1) := by
    rw [← Real.rpow_natCast (x^(((r:ℝ)-1)/2)) 2, ← Real.rpow_mul hx.le]
    congr 1
    ring
  calc
    _ = (x^(((r:ℝ)-1)/2))^(2 : ℕ) *
        (Real.exp (-((m+1:ℕ):ℝ)*x)*Real.exp (-((n+1:ℕ):ℝ)*x)) := by ring
    _ = _ := by
      rw [hpow, ← Real.exp_add]
      congr 2
      push_cast
      ring

/-- The finite source norm is exactly the existing energy, with all cross terms retained. -/
theorem norm_sum_gammaLaplaceAtom_sq (r : Ioi (0:ℝ)) (a : ℕ → ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, (a n : ℂ) • gammaLaplaceAtom r n‖^(2 : ℕ) =
      finiteGammaHankelEnergy a N r := by
  have hinner : inner ℂ (∑ n ∈ Finset.range N, (a n : ℂ) • gammaLaplaceAtom r n)
      (∑ n ∈ Finset.range N, (a n : ℂ) • gammaLaplaceAtom r n) =
      (finiteGammaHankelEnergy a N r : ℂ) := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, inner_gammaLaplaceAtom]
    unfold finiteGammaHankelEnergy
    push_cast
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (n:ℝ)+m+2=(m:ℝ)+n+2 by ring]
    ring
  calc
    _ = RCLike.re (inner ℂ (∑ n ∈ Finset.range N, (a n : ℂ) • gammaLaplaceAtom r n)
        (∑ n ∈ Finset.range N, (a n : ℂ) • gammaLaplaceAtom r n)) :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = _ := by rw [hinner]; rfl

private theorem gammaLaplaceFeature_four_coordinate (r : ℝ) (n : ℕ) :
    gammaLaplaceFeature r (4*(n+1)-1) = fun x =>
      (Real.exp (-4*x) : ℂ)^n * gammaLaplaceFeature r 3 x := by
  funext x
  have hidx : 4*(n+1)-1+1=4*(n+1) := by omega
  simp only [gammaLaplaceFeature, hidx, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/-- The kernel frequencies alone: all positive multiples of four. -/
def gammaSquarefulAtomSpan (r : Ioi (0:ℝ)) : Submodule ℂ HTGeometry.BurnolHalfLineL2 :=
  Submodule.span ℂ (Set.range (fun n : ℕ => gammaLaplaceAtom r (4*(n+1)-1)))

/-- Squareful atoms already span densely the entire additive completion. -/
theorem dense_gammaSquarefulAtomSpan (r : Ioi (0:ℝ)) :
    Dense (gammaSquarefulAtomSpan r : Set HTGeometry.BurnolHalfLineL2) := by
  have hperp : (gammaSquarefulAtomSpan r)ᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun g hg => ?_
    have hmom (n : ℕ) : ∫ x in Ioi (0:ℝ),
        (Real.exp (-4*x) : ℂ)^n * (gammaLaplaceFeature r 3 x*g x) = 0 := by
      have h := (Submodule.mem_orthogonal _ g).mp hg (gammaLaplaceAtom r (4*(n+1)-1))
        (Submodule.subset_span ⟨n, rfl⟩)
      rw [L2.inner_def] at h
      rw [← h]
      apply integral_congr_ae
      filter_upwards [gammaLaplaceAtom_ae r (4*(n+1)-1)] with x hx
      rw [hx, RCLike.inner_apply]
      have hreal : starRingEnd ℂ (gammaLaplaceFeature r (4*(n+1)-1) x) =
          gammaLaplaceFeature r (4*(n+1)-1) x := by
        simp only [gammaLaplaceFeature, Complex.conj_ofReal]
      rw [hreal, gammaLaplaceFeature_four_coordinate]
      ring
    have hz := HTGeometry.ae_eq_zero_of_integer_laplace_moments (by norm_num : (0:ℝ)<4)
      ((memLp_gammaLaplaceFeature r.property 3).integrable_mul (Lp.memLp g)) hmom
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hz, ae_restrict_mem measurableSet_Ioi] with x hx hxpos
    have hw : gammaLaplaceFeature r 3 x ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      exact mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hxpos _)) (Real.exp_ne_zero _)
    exact (mul_eq_zero.mp hx).resolve_left hw
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (Submodule.topologicalClosure_eq_top_iff.mpr hperp)

theorem gammaLaplaceAtom_ne_zero (r : Ioi (0:ℝ)) (n : ℕ) :
    gammaLaplaceAtom r n ≠ 0 := by
  intro hz
  have heq := (Lp.eq_zero_iff_ae_eq_zero.mp hz).symm.trans (gammaLaplaceAtom_ae r n)
  have hf : ∀ᵐ x ∂volume.restrict (Ioi (0:ℝ)), False := by
    filter_upwards [heq, ae_restrict_mem measurableSet_Ioi] with x hx hxpos
    have hw : gammaLaplaceFeature r n x ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      exact mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hxpos _)) (Real.exp_ne_zero _)
    exact hw hx.symm
  have hm := ae_iff.mp hf
  simp at hm

/-- No closable, possibly unbounded, partially defined linear operator can
carry every integer atom to its literal Möbius multiple in this completion. -/
theorem no_closable_gammaLaplace_mobius_operator (r : Ioi (0:ℝ)) :
    ¬ ∃ T : HTGeometry.BurnolHalfLineL2 →ₗ.[ℂ] HTGeometry.BurnolHalfLineL2,
      T.IsClosable ∧ ∀ n : ℕ,
        (gammaLaplaceAtom r n,
          (ArithmeticFunction.moebius (n+1) : ℂ) • gammaLaplaceAtom r n) ∈ T.graph := by
  rintro ⟨T, ⟨U, hU⟩, hT⟩
  let G := T.graph.topologicalClosure
  have hclosed : IsClosed (G : Set (HTGeometry.BurnolHalfLineL2 × HTGeometry.BurnolHalfLineL2)) :=
    isClosed_closure
  have hfour (n : ℕ) : (gammaLaplaceAtom r (4*(n+1)-1), 0) ∈ G := by
    apply Submodule.le_topologicalClosure
    have h := hT (4*(n+1)-1)
    rw [show 4*(n+1)-1+1=4*(n+1) by omega, mobius_four_mul_zero] at h
    simpa using h
  have hspan : ∀ v ∈ gammaSquarefulAtomSpan r, (v,0) ∈ G := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨n,rfl⟩ := hv; exact hfour n
    | zero => exact G.zero_mem
    | add x y _ _ hx hy => simpa using G.add_mem hx hy
    | smul c x _ hx => simpa using G.smul_mem c hx
  have hhor (v : HTGeometry.BurnolHalfLineL2) : (v,0) ∈ G :=
    (hclosed.preimage (continuous_id.prodMk continuous_const)).closure_subset_iff.mpr
      hspan (dense_gammaSquarefulAtomSpan r v)
  have hdiag : (gammaLaplaceAtom r 0,gammaLaplaceAtom r 0) ∈ G := by
    apply Submodule.le_topologicalClosure
    simpa using hT 0
  have hvertical : ((0 : HTGeometry.BurnolHalfLineL2),gammaLaplaceAtom r 0) ∈ G := by
    simpa using G.sub_mem hdiag (hhor (gammaLaplaceAtom r 0))
  change (0,gammaLaplaceAtom r 0) ∈ T.graph.topologicalClosure at hvertical
  rw [hU] at hvertical
  exact gammaLaplaceAtom_ne_zero r 0 (U.graph_fst_eq_zero_snd hvertical rfl)

end
end RHTower
