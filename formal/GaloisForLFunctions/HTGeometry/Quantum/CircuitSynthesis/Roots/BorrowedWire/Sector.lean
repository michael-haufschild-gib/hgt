import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.BorrowedWire.FivePhases

/-! # Cubic leakage suppression in each physical eigenphase sector -/

open Matrix Complex
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.BorrowedWire
noncomputable section

private abbrev M₂ := Matrix (Fin 2) (Fin 2) ℂ

/-- An equatorial rotation, expressed through its real diagonal and
complex transition amplitude on an arbitrary state of the control. -/
def sector (x : ℝ) (u : ℂ) : M₂ := pulse x u (star u)

/-- Phase shift for the two outside pulses in the five-pulse sequence. -/
def multiplier : ℂ := ⟨-1/4,Real.sqrt 15/4⟩

private theorem phase_add : multiplier+star multiplier= -(1/2) := by
  apply Complex.ext <;> norm_num [multiplier,Complex.add_re,Complex.add_im,Complex.div_re,Complex.div_im]

theorem multiplier_unit : multiplier*star multiplier=1 := by
  apply Complex.ext
  · change (-1/4:ℝ)*(-1/4) - (Real.sqrt 15/4)*(-(Real.sqrt 15/4))=1
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤15)]
  · change (-1/4:ℝ)*(-(Real.sqrt 15/4))+(Real.sqrt 15/4)*(-1/4)=0
    ring

/-- The palindrome of five phase-shifted copies of the same sector. -/
def five (x : ℝ) (u : ℂ) : M₂ :=
  let A := sector x (multiplier*u)
  let B := sector x (star multiplier*u)
  A*(B*sector x u*B)*A

private def paired (P : M₂) : Prop :=
  P 1 1=star (P 0 0) ∧ P 1 0= -star (P 0 1)

private theorem paired_sector (x : ℝ) (u : ℂ) : paired (sector x u) := by
  simp [paired,sector,pulse]

private theorem paired_mul {P Q : M₂} (hP : paired P) (hQ : paired Q) : paired (P*Q) := by
  obtain ⟨ha,hb⟩ := hP
  obtain ⟨hc,hd⟩ := hQ
  constructor <;> simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,hc,hd,star_add,star_mul,star_neg,star_star] <;> ring

private theorem det_sector (x : ℝ) (u : ℂ) : (sector x u).det=(x:ℂ)^2+u*star u := by
  simp [sector,pulse,Matrix.det_fin_two,pow_two]

private theorem complex_mass (u : ℂ) : u*star u=(Complex.normSq u:ℂ) := by
  exact Complex.mul_conj u

/-- On the entire two-dimensional control sector the five-pulse output
again has equal real diagonals, and the squared leakage has the stated
exact polynomial. This controls both control inputs. -/
theorem five_sector {x : ℝ} {u : ℂ} (hx : 0≤x) (hu : x^2+Complex.normSq u=1) :
    let q := Complex.normSq u
    let y := x*(1+q/2+3*q^2/8)
    ∃ v : ℂ, five x u=sector y v ∧ 0≤y ∧
      Complex.normSq v=q^3*(40+15*q+9*q^2)/64 ∧ y^2+Complex.normSq v=1 := by
  intro q y
  have hnorm : (x:ℂ)^2+u*star u=1 := by
    rw [complex_mass]
    exact_mod_cast hu
  obtain ⟨U,V,hQ⟩ := five_pulse (x:ℂ) u (star u) multiplier (star multiplier) phase_add multiplier_unit hnorm
  have hdiag : (x:ℂ)*(1+u*star u/2+3*(u*star u)^2/8)=(y:ℂ) := by
    rw [complex_mass]; dsimp only [y,q]; push_cast; rfl
  have hm : five x u=pulse (y:ℂ) U V := by
    rw [←hdiag]
    simpa only [five,sector,star_mul,star_star,mul_comm (star u)] using hQ
  have hform : paired (five x u) :=
    paired_mul (paired_mul (paired_sector ..) (paired_mul (paired_mul (paired_sector ..) (paired_sector ..))
      (paired_sector ..))) (paired_sector ..)
  rw [hm] at hform
  have hv : V=star U := neg_injective hform.2
  have he : five x u=sector y U := by rw [hm,hv]; rfl
  have hdet (a : ℂ) (ha : a*star a=1) : (sector x (a*u)).det=1 := by
    rw [det_sector,star_mul,show a*u*(star u*star a)=(a*star a)*(u*star u) by ring,ha,one_mul]
    exact hnorm
  have htotal : (five x u).det=1 := by
    simp only [five,Matrix.det_mul,hdet multiplier multiplier_unit,hdet (star multiplier) (by rwa [star_star,mul_comm]),
      det_sector,hnorm,mul_one,one_mul]
  rw [he,det_sector,complex_mass] at htotal
  have hreal : y^2+Complex.normSq U=1 := by exact_mod_cast htotal
  obtain ⟨hy,hpoly,_⟩ := five_pulse_leakage hx (Complex.normSq_nonneg u) hu
  exact ⟨U,he,hy,(show Complex.normSq U=1-y^2 by linarith only [hreal]).trans hpoly,hreal⟩

#print axioms five_sector
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.BorrowedWire
