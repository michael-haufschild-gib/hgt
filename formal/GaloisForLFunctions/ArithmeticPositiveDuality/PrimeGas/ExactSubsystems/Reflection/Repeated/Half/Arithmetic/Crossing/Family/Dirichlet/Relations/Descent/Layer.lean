import GaloisForLFunctions.HTGeometry.ExponentialPolynomialZeroBound
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Descent.Length

/-! # Conjugate coefficient elimination and the finite layer of shortest shell relations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Finset Set Real
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry.ExpZeroBound (expPoly card_lt_of_expPoly_eq_zero')

/-- Possible aligned real coefficients, including both orientations. -/
noncomputable def orientations (c d : ShellIntegers) : Finset ℝ := by
  classical
  let pairs := (coefficientRoots c).product (coefficientRoots d)
  exact (pairs.image (fun p => ‖p.1‖*‖p.2‖)) ∪ (pairs.image (fun p => -(‖p.1‖*‖p.2‖)))

theorem orientation_mem (ρ : ShellIntegers →+* ℂ) (c d : ShellIntegers) (x : ℝ)
    (magnitude : |x|=‖ρ c‖*‖ρ d‖) : x ∈ orientations c d := by
  classical
  have hit : (ρ c,ρ d) ∈ (coefficientRoots c).product (coefficientRoots d) :=
    Finset.mem_product.mpr ⟨coefficient_mem ρ c,coefficient_mem ρ d⟩
  rcases le_total 0 x with pos | neg
  · exact Finset.mem_union_left _ (mem_image.mpr ⟨(ρ c,ρ d),hit,magnitude.symm.trans (abs_of_nonneg pos)⟩)
  · apply Finset.mem_union_right
    refine mem_image.mpr ⟨(ρ c,ρ d),hit,?_⟩
    change -(‖ρ c‖*‖ρ d‖)=x
    rw [← magnitude,abs_of_nonpos neg,neg_neg]

private theorem label_energy_injective : Function.Injective energy := by
  intro a b eq
  have h := congrArg exp eq
  simp only [energy,exp_log (Nat.cast_pos.mpr a.pos),exp_log (Nat.cast_pos.mpr b.pos)] at h
  exact PNat.coe_injective (Nat.cast_injective (R := ℝ) h)

/-- A finite menu at each shell permits finitely many zeros among all
nonzero real coefficient patterns. -/
theorem finite_pattern_zeros {k : ℕ} (a : Fin k → ℕ+) (inj : Function.Injective a) (C : Fin k → Finset ℝ) :
    {s : ℝ | ∃ f : Fin k → ℝ, (∀ i, f i ∈ C i) ∧ (∃ i, f i ≠ 0) ∧
      (∑ i, f i*shellPower s (a i))=0}.Finite := by
  classical
  let Z (f : Fin k → ℝ) := {s : ℝ | (∃ i, f i ≠ 0) ∧ (∑ i, f i*shellPower s (a i))=0}
  have finite (f : Fin k → ℝ) : (Z f).Finite := by
    by_contra inf
    let E (i : Fin k) := energy (a i)
    let P (i : Fin k) := Polynomial.C (f i)
    obtain ⟨s,hs⟩ := Set.Infinite.nonempty inf
    obtain ⟨i,hi⟩ := hs.1
    have live : ∃ i, P i ≠ 0 := ⟨i,by simpa only [P,ne_eq,Polynomial.C_eq_zero] using hi⟩
    obtain ⟨T,sub,card⟩ := Set.Infinite.exists_subset_card_eq inf (∑ i, ((P i).natDegree+1))
    have bound := card_lt_of_expPoly_eq_zero' E P (label_energy_injective.comp inj) live T (fun v hv => by
      have eq := (sub hv).2
      simpa only [expPoly,P,E,Polynomial.eval_C,shellPower_exp,mul_comm v] using eq)
    exact bound.ne card
  let T := Fintype.piFinset C
  apply (T.finite_toSet.biUnion (fun f _ => finite f)).subset
  rintro v ⟨f,choice,live,zero⟩
  exact Set.mem_iUnion.mpr ⟨f,Set.mem_iUnion.mpr ⟨Fintype.mem_piFinset.mpr choice,live,zero⟩⟩

private def bar (z : ShellIntegers) : ShellIntegers :=
  ⟨conj (z : ℂ),z.property.map (starRingEnd ℂ).toIntAlgHom⟩

private theorem coe_live {z : ShellIntegers} (nz : z ≠ 0) : (z : ℂ) ≠ 0 := fun h => nz (Subtype.ext h)

/-- A complex coefficient relation on real shell weights either loses at
least one shell by conjugation or aligns along a single real line. -/
theorem eliminate_or_align {k : ℕ} {v : ℝ} (a : Fin k → ℕ+) (inj : Function.Injective a)
    (b : Fin k → ShellIntegers) (live : ∀ i, b i ≠ 0) (r : Fin k)
    (zero : (∑ i, (b i : ℂ)*(shellPower v (a i) : ℂ))=0) :
    (∃ l, l<k ∧ shellRelationLength v l) ∨
      ∃ f : Fin k → ℝ, (∀ i, |f i|=‖(b i : ℂ)‖*‖(b r : ℂ)‖) ∧
        (∀ i, (f i : ℂ)=(b i : ℂ)*conj (b r : ℂ)) ∧
        (∃ i, f i ≠ 0) ∧ (∑ i, f i*shellPower v (a i))=0 := by
  classical
  let w (i : Fin k) := (shellPower v (a i) : ℂ)
  let z (i : Fin k) := b i*bar (b r)-bar (b i)*b r
  have back : (∑ i, conj (b i : ℂ)*w i)=0 := by
    simpa only [map_sum,map_mul,Complex.conj_ofReal,map_zero,w] using congrArg conj zero
  have forward : (∑ i, (b i : ℂ)*w i)=0 := zero
  by_cases some : ∃ i, z i ≠ 0
  · left
    apply shorter_of_zero_coefficient a inj z some ⟨r,by simp only [z,mul_comm (b r),sub_self]⟩
    change (∑ i, ((b i : ℂ)*conj (b r : ℂ)-conj (b i : ℂ)*(b r : ℂ))*w i)=0
    calc _ = conj (b r : ℂ)*(∑ i, (b i : ℂ)*w i)-(b r : ℂ)*(∑ i, conj (b i : ℂ)*w i) := by
              rw [mul_sum,mul_sum,← sum_sub_distrib]
              exact sum_congr rfl fun i _ => by ring
         _ = 0 := by rw [forward,back,mul_zero,mul_zero,sub_zero]
  · right
    push Not at some
    let aligned (i : Fin k) := (b i : ℂ)*conj (b r : ℂ)
    have real (i : Fin k) : ((aligned i).re : ℂ)=aligned i := by
      apply Complex.conj_eq_iff_re.mp
      have eq := congrArg ((↑) : ShellIntegers → ℂ) (some i)
      change (b i : ℂ)*conj (b r : ℂ)-conj (b i : ℂ)*(b r : ℂ)=0 at eq
      simp only [aligned,map_mul,starRingEnd_self_apply]
      exact (sub_eq_zero.mp eq).symm
    have mag (i : Fin k) : |(aligned i).re|=‖(b i : ℂ)‖*‖(b r : ℂ)‖ := by
      rw [← Real.norm_eq_abs,← Complex.norm_real,real]
      simp only [aligned,norm_mul,Complex.norm_conj]
    refine ⟨fun i => (aligned i).re,mag,real,⟨r,?_⟩,?_⟩
    · intro h
      change (aligned r).re=0 at h
      have m := mag r
      rw [h,abs_zero] at m
      exact (mul_pos (norm_pos_iff.mpr (coe_live (live r))) (norm_pos_iff.mpr (coe_live (live r)))).ne' m.symm
    · apply Complex.ofReal_eq_zero.mp
      rw [Complex.ofReal_sum]
      simp only [Complex.ofReal_mul,real]
      calc (∑ i, aligned i*w i) = conj (b r : ℂ)*(∑ i, (b i : ℂ)*w i) := by
             rw [mul_sum]; exact sum_congr rfl fun i _ => by dsimp only [aligned]; ring
           _ = 0 := by rw [forward,mul_zero]

/-- Signed zeros from the finitely many orientations of conjugate coefficients. -/
def alignedOrders {k : ℕ} (a : Fin k → ℕ+) (c : Fin k → ShellIntegers) (r : Fin k) :=
  {v : ℝ | ∃ f : Fin k → ℝ, (∀ i, f i ∈ orientations (c i) (c r)) ∧ (∃ i, f i ≠ 0) ∧
      (∑ i, f i*shellPower v (a i))=0}

/-- At the signed target a fixed source relation either has an aligned
coefficient pattern or yields a strictly shorter shell relation. -/
theorem descent_on_support {t u : ℝ} (ht : 0<t) {k : ℕ} (a : Fin k → ℕ+)
    (c : Fin k → ShellIntegers) (r : Fin k) (inj : Function.Injective a) (live : ∀ i, c i ≠ 0)
    (zero : (∑ i, (c i : ℂ)*(shellPower t (a i) : ℂ))=0) (hit : u ∈ accumulated t) :
    shellRelationLength u k ∧ (u ∈ alignedOrders a c r ∪ Neg.neg ⁻¹' alignedOrders a c r ∨
      ∃ l, l<k ∧ shellRelationLength u l) := by
  classical
  let Z := alignedOrders a c r
  have hk : 0<k := Nat.zero_lt_of_lt r.isLt
  obtain ⟨hu,m,hm,force⟩ := hit
  have atSign (v : ℝ) (s : TorsionSpecialization m t v) :
      shellRelationLength v k ∧ (v ∈ Z ∨ ∃ l, l<k ∧ shellRelationLength v l) := by
    obtain ⟨ρ,ω,unit,keep⟩ := coefficient_specialization s
    have integral (n : ℕ+) : IsIntegral ℤ (ω n) :=
      IsIntegral.of_pow hm (by rw [unit]; exact isIntegral_one)
    let b (i : Fin k) : ShellIntegers := ⟨ρ (c i)*ω (a i),
      ((integralClosure.isIntegral (c i)).map ρ.toIntAlgHom).mul (integral (a i))⟩
    have nz (i : Fin k) : b i ≠ 0 := by
      have coeff := (coefficient_injective ρ).ne (live i)
      rw [map_zero] at coeff
      have phase : ω (a i) ≠ 0 := norm_pos_iff.mp (by rw [phase_norm hm (unit _)]; exact zero_lt_one)
      exact fun z => mul_ne_zero coeff phase (congrArg ((↑) : ShellIntegers → ℂ) z)
    have erase : (∑ i, (b i : ℂ)*(shellPower v (a i) : ℂ))=0 := keep a c zero
    refine ⟨⟨a,b,hk,inj,nz,erase⟩,?_⟩
    rcases eliminate_or_align a inj b nz r erase with small | ⟨f,mag,_,active,root⟩
    · exact Or.inr small
    · refine Or.inl ⟨f,fun i => orientation_mem ρ (c i) (c r) (f i) ?_,active,root⟩
      have eq := mag i
      change |f i|=‖ρ (c i)*ω (a i)‖*‖ρ (c r)*ω (a r)‖ at eq
      simpa only [norm_mul,phase_norm hm (unit (a i)),phase_norm hm (unit (a r)),mul_one] using eq
  rcases (scaled_forcing_iff ht hu hm).mp force with plus | minus
  · obtain ⟨len,h⟩ := atSign u plus
    exact ⟨len,h.imp (fun z => Or.inl z) id⟩
  · obtain ⟨len,h⟩ := atSign (-u) minus
    have reflect {j : ℕ} (l : shellRelationLength (-u) j) : shellRelationLength u j := by
      simpa only [neg_neg] using reflected_length l
    refine ⟨reflect len,h.imp (fun z => Or.inr z) ?_⟩
    rintro ⟨l,lt,hit⟩
    exact ⟨l,lt,reflect hit⟩

/-- Only finitely many targets of a source packet can escape strict descent. -/
theorem descent_of_packet {t : ℝ} (ht : 0<t) {k : ℕ} (packet : shellRelationLength t k) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ u ∈ accumulated t, shellRelationLength u k ∧
      (u ∈ E ∨ ∃ l, l<k ∧ shellRelationLength u l) := by
  obtain ⟨a,c,hk,inj,live,zero⟩ := packet
  let r : Fin k := ⟨0,hk⟩
  have fin : (alignedOrders a c r).Finite := finite_pattern_zeros a inj _
  exact ⟨_,fin.union (fin.preimage neg_injective.injOn),
    fun _ hit => descent_on_support ht a c r inj live zero hit⟩

/-- Forced readings at the same minimum relation length as the source. -/
def sameLength (t : ℝ) := {u ∈ accumulated t | shortest u=shortest t}

theorem shortest_monotone {t u : ℝ} (ht : 0<t) (res : Resonant t) (hit : u ∈ accumulated t) :
    shortest u ≤ shortest t := by
  obtain ⟨_,_,all⟩ := descent_of_packet ht (shortest_attained (resonance_has_length res))
  exact shortest_le (all u hit).1

theorem finite_sameLength {t : ℝ} (ht : 0<t) (res : Resonant t) : (sameLength t).Finite := by
  obtain ⟨E,finite,all⟩ := descent_of_packet ht (shortest_attained (resonance_has_length res))
  apply finite.subset
  rintro u ⟨hit,eq⟩
  rcases (all u hit).2 with inside | ⟨l,lt,h⟩
  · exact inside
  · have low := shortest_le h
    rw [eq] at low
    exact (lt.not_ge low).elim

#print axioms finite_pattern_zeros
#print axioms eliminate_or_align
#print axioms descent_on_support
#print axioms descent_of_packet
#print axioms shortest_monotone
#print axioms finite_sameLength

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
