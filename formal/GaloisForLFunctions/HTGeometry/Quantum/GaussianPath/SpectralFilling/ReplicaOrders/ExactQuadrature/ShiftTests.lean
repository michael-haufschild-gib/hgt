import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.Dephasing

/-! # Translates of one positive spectral polynomial determine every clock coefficient -/
open Finset
open scoped ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section
variable {I J : Type*} [Fintype J]

/-- Testing against a conjugate wave reads exactly its whole
equal-frequency coefficient, including all collisions. -/
theorem read_frequency (S : Finset I) (E : I → ℝ) (c : I → ℂ) {k : I} (hk : k∈S) (a : ℝ) :
    average (gaps S E).toList (fun u => (∑ i∈S, c i*wave (E i) u)*conj (wave (E k) u)) a=
      ∑ i∈S.filter (fun i => E i=E k), c i := by
  have he (u : ℝ) : (∑ i∈S, c i*wave (E i) u)*conj (wave (E k) u)=
      ∑ i∈S, c i*wave (E i-E k) u := by
    rw [Finset.sum_mul]
    exact sum_congr rfl fun i _ => by rw [mul_assoc,wave_diff]
  rw [show (fun u => (∑ i∈S, c i*wave (E i) u)*conj (wave (E k) u))=_ from funext he,
    average_sum,Finset.sum_filter]
  apply sum_congr rfl
  intro i hi
  rw [average_scale,gap_phase S E hi hk]
  split_ifs <;> simp

/-- A frequency-dependent multiplier cannot cancel strictly positive
weights on any one occupied frequency. -/
theorem multiplier_zero (S : Finset I) (E b : I → ℝ) (hb : ∀ i∈S, 0<b i) (m : ℝ → ℂ)
    (h : ∀ u, ∑ i∈S, (b i:ℂ)*m (E i)*wave (E i) u=0) {k : I} (hk : k∈S) : m (E k)=0 := by
  classical
  let F := S.filter fun i => E i=E k
  have he := read_frequency S E (fun i => (b i:ℂ)*m (E i)) hk 0
  simp only [h,zero_mul,average_const] at he
  have hsum : ∑ i∈F, (b i:ℂ)*m (E i)=((∑ i∈F, b i:ℝ):ℂ)*m (E k) := by
    rw [Complex.ofReal_sum,Finset.sum_mul]
    exact sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
  have hp : 0<∑ i∈F, b i := sum_pos' (fun i hi => (hb i (mem_filter.mp hi).1).le)
    ⟨k,mem_filter.mpr ⟨hk,rfl⟩,hb k hk⟩
  have hn : ((∑ i∈F, b i:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp.ne'
  exact (mul_eq_zero.mp (hsum.symm.trans he.symm)).resolve_left hn

/-- A positive spectral polynomial with the chosen frequencies. -/
def polynomial (S : Finset I) (E b : I → ℝ) (u : ℝ) : ℂ := ∑ i∈S, (b i:ℂ)*wave (E i) u

/-- Exact integration of every translate of one polynomial with
positive coefficients is equivalent to exact integration of each of
its frequencies. The sampling weights may even be signed. -/
theorem shifted_clock_iff (S : Finset I) (E b : I → ℝ) (hb : ∀ i∈S, 0<b i) (p t : J → ℝ) :
    (∀ u, ∑ j, (p j:ℂ)*polynomial S E b (u+t j)=
      ∑ i∈S, if E i=0 then (b i:ℂ) else 0) ↔
    ∀ i∈S, ∑ j, (p j:ℂ)*wave (E i) (t j)=if E i=0 then 1 else 0 := by
  let m (w : ℝ) := ∑ j, (p j:ℂ)*wave w (t j)
  let z (w : ℝ) : ℂ := if w=0 then 1 else 0
  have expand (u : ℝ) : ∑ j, (p j:ℂ)*polynomial S E b (u+t j)=
      ∑ i∈S, (b i:ℂ)*m (E i)*wave (E i) u := by
    simp only [polynomial,Finset.mul_sum,wave_add]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    dsimp only [m]
    rw [Finset.mul_sum,Finset.sum_mul]
    exact sum_congr rfl fun j _ => by ring
  have constant (u : ℝ) : (∑ i∈S, if E i=0 then (b i:ℂ) else 0)=
      ∑ i∈S, (b i:ℂ)*z (E i)*wave (E i) u := by
    apply sum_congr rfl
    intro i _
    by_cases he : E i=0 <;> simp [z,he,wave]
  constructor
  · intro h
    have hz (u : ℝ) : ∑ i∈S, (b i:ℂ)*(m (E i)-z (E i))*wave (E i) u=0 := by
      simp only [mul_sub,sub_mul,sum_sub_distrib,←expand,←constant,h,sub_self]
    intro k hk
    exact sub_eq_zero.mp (multiplier_zero S E b hb (fun w => m w-z w) hz hk)
  · intro h u
    rw [expand,constant u]
    exact sum_congr rfl fun i hi => by rw [show m (E i)=z (E i) from h i hi]

#print axioms shifted_clock_iff
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
