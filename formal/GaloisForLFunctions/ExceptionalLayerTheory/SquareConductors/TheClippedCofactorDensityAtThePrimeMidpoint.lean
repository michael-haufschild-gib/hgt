import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheTotientTermInTheReflectedCompositePrice
import GaloisForLFunctions.ExceptionalLayerTheory.TruncatedHarmonicDensityOfDivisorFloors

/-!
# Discrete cofactor correction to the reflected interval lengths

Summing a single clipped length gives a harmonic number at a sharp floor.
The three half-endpoint terms cancel exactly. Each divisor scale m then
costs at most a constant times the lesser of m and P²/m.
-/

noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def clippedRay (N P v : ℕ) : ℝ := max ((N:ℝ)/v-P) 0

/-- Difference of right and left prime interval lengths for the same cofactor. -/
def reflectedCofactorLength (n P v : ℕ) : ℝ :=
  clippedRay (4*n) P v-2*clippedRay (3*n) P v+clippedRay (2*n) P v

private def latticeLength (n P : ℕ) : ℝ :=
  ∑ v ∈ Icc 1 (4*n/P),reflectedCofactorLength n P v

/-- Sum of the two clipped interval lengths on the primitive cofactors. -/
def primitiveCofactorLength (n P : ℕ) : ℝ :=
  ∑ v ∈ (Icc 1 (4*n/P)).filter (n.Coprime ·),reflectedCofactorLength n P v

private theorem ray_range {N P T : ℕ} (hP : 0 < P) (hT : N/P ≤ T) :
    (∑ v ∈ Icc 1 T,clippedRay N P v)=
      (P:ℝ)*(((N:ℝ)/P)*(harmonic (N/P):ℝ)-(N/P:ℕ)) := by
  let k := N/P
  have hsmall : (∑ v ∈ Icc 1 k,clippedRay N P v)=∑ v ∈ Icc 1 T,clippedRay N P v := by
    apply sum_subset (Icc_subset_Icc_right hT)
    intro v hv hnot
    have hv0 := (mem_Icc.mp hv).1
    have hvk : k < v := lt_of_not_ge (fun h => hnot (mem_Icc.mpr ⟨hv0,h⟩))
    have hgt := (Nat.div_lt_iff_lt_mul hP).mp hvk
    have hreal : (N:ℝ) ≤ (P:ℝ)*v := by exact_mod_cast (hgt.le.trans_eq (Nat.mul_comm v P))
    exact max_eq_right (sub_nonpos.mpr ((div_le_iff₀ (Nat.cast_pos.mpr hv0)).mpr hreal))
  have hterm (v : ℕ) (hv : v ∈ Icc 1 k) :
      clippedRay N P v=(N:ℝ)*(1/(v:ℝ))-P := by
    obtain ⟨hv0,hvk⟩ := mem_Icc.mp hv
    have hle := (Nat.le_div_iff_mul_le hP).mp hvk
    have hr : (P:ℝ)*v ≤ N := by exact_mod_cast (Nat.mul_comm P v).le.trans hle
    rw [clippedRay,max_eq_left (sub_nonneg.mpr ((le_div_iff₀ (Nat.cast_pos.mpr hv0)).mpr hr)),mul_one_div]
  have hh : (∑ j ∈ Icc 1 k,1/(j:ℝ))=(harmonic k:ℝ) := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    simp only [Rat.cast_inv,Rat.cast_natCast,one_div]
  rw [←hsmall,sum_congr rfl hterm,sum_sub_distrib,←mul_sum,hh,sum_const,Nat.card_Icc,
    Nat.add_one_sub_one,nsmul_eq_mul]
  change (N:ℝ)*(harmonic k:ℝ)-k*P=(P:ℝ)*(((N:ℝ)/P)*(harmonic k:ℝ)-k)
  field_simp [Nat.cast_ne_zero.mpr hP.ne']
  <;> ring

private def rayMain (N P : ℕ) : ℝ :=
  N*(Real.log ((N:ℝ)/P)+Real.eulerMascheroniConstant-1)+(P:ℝ)/2

private theorem ray_error {N P T : ℕ} (hN : 0 < N) (hP : 0 < P) (hT : N/P ≤ T) :
    |(∑ v ∈ Icc 1 T,clippedRay N P v)-rayMain N P| ≤ 4*(P:ℝ)^2/N := by
  let x := (N:ℝ)/P
  have hN' := (Nat.cast_pos (α:=ℝ)).mpr hN
  have hP' := (Nat.cast_pos (α:=ℝ)).mpr hP
  have hx := div_pos hN' hP'
  have hlo : ((N/P:ℕ):ℝ) ≤ x := Nat.cast_div_le
  have hhi : x ≤ ((N/P:ℕ):ℝ)+1 := by
    apply (div_le_iff₀ hP').mpr
    exact_mod_cast ((Nat.lt_mul_div_succ N hP).le.trans_eq (Nat.mul_comm ..))
  have h := mul_le_mul_of_nonneg_left (harmonic_endpoint hx hlo hhi) hP'.le
  have hmain : rayMain N P = (P:ℝ)*(x*(Real.log x+Real.eulerMascheroniConstant-1)+1/2) := by
    dsimp only [rayMain,x]
    field_simp [hP'.ne']
    <;> ring
  rw [ray_range hP hT,hmain,←mul_sub,abs_mul,abs_of_nonneg hP'.le]
  apply h.trans_eq
  dsimp only [x]
  field_simp [hN'.ne',hP'.ne']
  <;> ring

private theorem length_height (n P v : ℕ) :
    0 ≤ reflectedCofactorLength n P v ∧ reflectedCofactorLength n P v ≤ P := by
  simp only [reflectedCofactorLength,clippedRay,Nat.cast_mul,Nat.cast_ofNat,mul_div_assoc,max_def]
  split_ifs <;> constructor <;> linarith only [*,Nat.cast_nonneg (α:=ℝ) P]

/-- Cancellation of all three harmonic endpoint terms in the lattice sum. -/
theorem clipped_lattice_density_error {m P : ℕ} (hm : 0 < m) (hP : 0 < P) :
    |latticeLength m P-reflectedDensity*m| ≤
      max (4+|reflectedDensity|) 6 * min (m:ℝ) ((P:ℝ)^2/m) := by
  let T := 4*m/P
  let H (k : ℕ) := ∑ v ∈ Icc 1 T,clippedRay (k*m) P v
  have hsum : latticeLength m P=H 4-2*H 3+H 2 := by
    simp only [latticeLength,reflectedCofactorLength,H,T,sum_add_distrib,sum_sub_distrib,mul_sum]
  have hm' := (Nat.cast_pos (α:=ℝ)).mpr hm
  have hp' := (Nat.cast_pos (α:=ℝ)).mpr hP
  have hmain : rayMain (4*m) P-2*rayMain (3*m) P+rayMain (2*m) P=reflectedDensity*m := by
    have hl (k : ℕ) (hk : 0 < k) : Real.log ((k*m:ℕ)/(P:ℝ))=Real.log k+Real.log m-Real.log P := by
      rw [Nat.cast_mul,Real.log_div (by positivity) hp'.ne',Real.log_mul (by positivity) hm'.ne']
    have h4 : Real.log 4=2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
    dsimp only [rayMain,reflectedDensity]
    rw [hl 4 (by decide),hl 3 (by decide),hl 2 (by decide)]
    push_cast; rw [h4]; ring
  have err (k : ℕ) (hk : 0 < k) (hk4 : k ≤ 4) :
      |H k-rayMain (k*m) P| ≤ 4*(P:ℝ)^2/(k*m:ℕ) :=
    ray_error (Nat.mul_pos hk hm) hP (Nat.div_le_div_right (Nat.mul_le_mul_right m hk4))
  have ef := abs_le.mp (err 4 (by decide) (by decide))
  have et := abs_le.mp (err 3 (by decide) (by decide))
  have es := abs_le.mp (err 2 (by decide) (by decide))
  have hlarge : |latticeLength m P-reflectedDensity*m| ≤ 6*((P:ℝ)^2/m) := by
    rw [hsum,abs_le]
    push_cast at ef et es
    have f (k : ℝ) : 4*(P:ℝ)^2/(k*m)=(4/k)*((P:ℝ)^2/m) := by
      simp only [div_eq_mul_inv,mul_inv_rev]; ring
    rw [f 4] at ef
    rw [f 3] at et
    rw [f 2] at es
    have hpos : 0 ≤ (P:ℝ)^2/m := by positivity
    constructor <;> linarith only [ef.1,ef.2,et.1,et.2,es.1,es.2,hmain,hpos]
  have hn : 0 ≤ latticeLength m P := sum_nonneg fun v _ => (length_height m P v).1
  have hheight : latticeLength m P ≤ 4*(m:ℝ) := by
    have h := sum_le_sum (s:=Icc 1 T) (fun v _ => (length_height m P v).2)
    simp only [sum_const,Nat.card_Icc,Nat.add_one_sub_one,nsmul_eq_mul] at h
    have hdiv : T*P ≤ 4*m := Nat.div_mul_le_self _ _
    exact h.trans (by exact_mod_cast hdiv)
  have hsmall := (abs_sub (latticeLength m P) (reflectedDensity*m)).trans
    (add_le_add_right ((abs_of_nonneg hn).le.trans hheight) |reflectedDensity*m|)
  rw [abs_mul,abs_of_nonneg hm'.le] at hsmall
  rcases le_total (m:ℝ) ((P:ℝ)^2/m) with h | h
  · rw [min_eq_left h]
    apply hsmall.trans
    rw [←add_mul]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hm'.le
  · rw [min_eq_right h]
    exact hlarge.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

#print axioms clipped_lattice_density_error

private theorem length_on_divisor {n d : ℕ} (hd : d ∈ n.divisors) (P w : ℕ) :
    reflectedCofactorLength n P (d*w)=reflectedCofactorLength (n/d) P w := by
  have hd0 := Nat.pos_of_mem_divisors hd
  have hn := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
  have he (k : ℕ) : ((k*n:ℕ):ℝ)/(d*w:ℕ)=((k*(n/d):ℕ):ℝ)/w := by
    calc _ = ((k*((n/d)*d):ℕ):ℝ)/(d*w:ℕ) := by rw [hn]
         _ = _ := by
           push_cast
           simp only [div_eq_mul_inv,mul_inv_rev]
           have h := mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hd0.ne' : (d:ℝ) ≠ 0)
           linear_combination (k:ℝ)*((n/d:ℕ):ℝ)*(w:ℝ)⁻¹ * h
  simp only [reflectedCofactorLength,clippedRay,he]

private theorem primitive_length_inversion {n : ℕ} (hn : 0 < n) (P : ℕ) :
    primitiveCofactorLength n P=∑ d ∈ n.divisors,(μ d:ℝ)*latticeLength (n/d) P := by
  classical
  let L := reflectedCofactorLength n P
  rw [primitiveCofactorLength,sum_filter]
  calc _ = ∑ v ∈ Icc 1 (4*n/P),∑ d ∈ n.divisors, if d ∣ v then (μ d:ℝ)*L v else 0 := by
             apply sum_congr rfl
             intro v _
             rw [show (if n.Coprime v then reflectedCofactorLength n P v else 0)=
               (if n.Coprime v then (1:ℝ) else 0)*L v by split_ifs <;> simp [L],
               reflected_coprime_indicator hn,sum_mul]
             exact sum_congr rfl fun d _ => by split_ifs <;> simp
       _ = _ := by
             rw [sum_comm]
             apply sum_congr rfl
             intro d hd
             have hdiv := Nat.dvd_of_mem_divisors hd
             have hcut : 4*n/P/d=4*(n/d)/P := by
               rw [Nat.div_div_eq_div_mul,Nat.mul_comm P d,←Nat.div_div_eq_div_mul,Nat.mul_div_assoc _ hdiv]
             rw [←sum_filter,_root_.RHTower.Sieve.sum_filter_dvd_eq_sum_scaled (Nat.pos_of_mem_divisors hd),
               hcut,latticeLength,mul_sum]
             exact sum_congr rfl fun v _ => congrArg (fun z => (μ d:ℝ)*z) (length_on_divisor hd P v)

/-- The discrete primitive length has its totient center at every integer.
Divisor scales close to the prime cutoff control its remaining error. -/
theorem primitive_clipped_density_error {n P : ℕ} (hn : 0 < n) (hp : 0 < P) :
    |primitiveCofactorLength n P-reflectedDensity*n.totient| ≤ max (4+|reflectedDensity|) 6 *
      ∑ d ∈ n.divisors,|(μ d:ℝ)|*min ((n/d:ℕ):ℝ) ((P:ℝ)^2/(n/d:ℕ)) := by
  have he : primitiveCofactorLength n P-reflectedDensity*n.totient=
      ∑ d ∈ n.divisors,(μ d:ℝ)*(latticeLength (n/d) P-reflectedDensity*(n/d:ℕ)) := by
    rw [primitive_length_inversion hn,_root_.RHTower.Sieve.totient_eq_sum_moebius_mul n hn,mul_sum,
      ←sum_sub_distrib]
    exact sum_congr rfl fun d _ => by ring
  rw [he,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  have hm := Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_mem_divisors hd)
  rw [abs_mul,mul_left_comm (max _ _)]
  exact mul_le_mul_of_nonneg_left (clipped_lattice_density_error hm hp) (abs_nonneg _)

#print axioms primitive_clipped_density_error

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
