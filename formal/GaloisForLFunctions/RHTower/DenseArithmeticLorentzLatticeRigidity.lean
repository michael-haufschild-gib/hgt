import GaloisForLFunctions.RHTower.RationalHurwitzLorentzBoost
import GaloisForLFunctions.RHTower.SeamSpectrumDensity

/-!
# Dense arithmetic Lorentz-lattice rigidity

The prime-log weld is dense in the archimedean rate line.  A horizontal character turns it into
a dense family of Lorentz boosts.  If all those boosts act in one fixed rank-two integral frame,
their traces are integral on a dense set.  Continuity then forces the Lorentz trace to be integral
everywhere, contradicting its value `5/2` at rapidity `log 2` unless horizontal grade is zero.

Unlike integral light-cone ghost descent, the common frame permits individual nontrivial integral
hyperbolic matrices.  Rigidity comes from one finite-rank lattice carrying the full dense prime
action.
-/

open Set

namespace RHTower

noncomputable section

/-- Trace of the certified rank-two Lorentz boost. -/
theorem trace_lorentzBoost (u : ℝ) :
    Matrix.trace (lorentzBoost u) = 2 * Real.cosh u := by
  simp [Matrix.trace, lorentzBoost, Fin.sum_univ_two]
  ring

/-- Trace-level consequence of descent of the prime-weld Lorentz action to an integral lattice. -/
def PrimeWeldLorentzIntegralTraceDescent (a : ℝ) : Prop :=
  ∀ x : ℝ, x ∈ GaloisForLFunctions.RHTower.primeLogLattice →
    ∃ k : ℤ, Matrix.trace (lorentzBoost (a * x)) = (k : ℝ)

/-- One prime-independent lattice frame for the full Lorentz action of the prime-log weld.
`intertwine` says that every boost has integer coordinates in the same invertible basis. -/
structure PrimeWeldIntegralLorentzLatticeFrame (a : ℝ) where
  basis : Matrix.GeneralLinearGroup (Fin 2) ℝ
  coordinates : ∀ x : ℝ,
    x ∈ GaloisForLFunctions.RHTower.primeLogLattice → Matrix (Fin 2) (Fin 2) ℤ
  intertwine : ∀ (x : ℝ)
      (hx : x ∈ GaloisForLFunctions.RHTower.primeLogLattice),
    lorentzBoost (a * x) * basis.val =
      basis.val * (coordinates x hx).map (Int.castRingHom ℝ)

/-- A common integral lattice frame makes every prime-weld boost trace integral. -/
theorem PrimeWeldIntegralLorentzLatticeFrame.traceDescent
    {a : ℝ} (F : PrimeWeldIntegralLorentzLatticeFrame a) :
    PrimeWeldLorentzIntegralTraceDescent a := by
  intro x hx
  let A : Matrix (Fin 2) (Fin 2) ℤ := F.coordinates x hx
  let AReal : Matrix (Fin 2) (Fin 2) ℝ := A.map (Int.castRingHom ℝ)
  have hintertwine : lorentzBoost (a * x) * F.basis.val = F.basis.val * AReal := by
    simpa [A, AReal] using F.intertwine x hx
  have hconj :
      lorentzBoost (a * x) = F.basis.val * AReal * F.basis.inv := by
    calc
      lorentzBoost (a * x) = lorentzBoost (a * x) * 1 := by simp
      _ = lorentzBoost (a * x) * (F.basis.val * F.basis.inv) := by
        rw [F.basis.val_inv]
      _ = (lorentzBoost (a * x) * F.basis.val) * F.basis.inv := by
        rw [Matrix.mul_assoc]
      _ = F.basis.val * AReal * F.basis.inv := by rw [hintertwine]
  refine ⟨Matrix.trace A, ?_⟩
  rw [hconj, Matrix.trace_mul_cycle]
  rw [F.basis.inv_val]
  simp only [Matrix.one_mul]
  exact (AddMonoidHom.map_trace (Int.castRingHom ℝ) A).symm

/-- **Dense-discrete rigidity.** Integral trace descent of the dense prime-weld boost forces
horizontal grade zero. -/
theorem eq_zero_of_primeWeldLorentzIntegralTraceDescent
    {a : ℝ} (h : PrimeWeldLorentzIntegralTraceDescent a) : a = 0 := by
  by_contra ha
  let f : ℝ → ℝ := fun x => 2 * Real.cosh (a * x)
  have hf : Continuous f := by
    fun_prop
  have hUopen : IsOpen (f ⁻¹' Set.Ioo 2 3) :=
    isOpen_Ioo.preimage hf
  have hx0 : Real.log 2 / a ∈ f ⁻¹' Set.Ioo (2 : ℝ) 3 := by
    have ha' : a * (Real.log 2 / a) = Real.log 2 := by
      field_simp
    change 2 < f (Real.log 2 / a) ∧ f (Real.log 2 / a) < 3
    rw [show f (Real.log 2 / a) = 2 * Real.cosh (Real.log 2) by simp [f, ha']]
    rw [Real.cosh_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hUne : (f ⁻¹' Set.Ioo (2 : ℝ) 3).Nonempty := ⟨_, hx0⟩
  obtain ⟨x, hxU, hxGamma⟩ :=
    (dense_iff_inter_open.mp GaloisForLFunctions.RHTower.primeLogLattice_dense)
      (f ⁻¹' Set.Ioo (2 : ℝ) 3) hUopen hUne
  obtain ⟨k, hk⟩ := h x hxGamma
  have hkf : f x = (k : ℝ) := by
    rw [← hk, trace_lorentzBoost]
  have hkBounds : (2 : ℝ) < (k : ℝ) ∧ (k : ℝ) < 3 := by
    simpa [hkf] using hxU
  have hkLower : (2 : ℤ) < k := by exact_mod_cast hkBounds.1
  have hkUpper : k < (3 : ℤ) := by exact_mod_cast hkBounds.2
  omega

/-- Integral trace descent is possible exactly at neutral horizontal grade. -/
theorem primeWeldLorentzIntegralTraceDescent_iff (a : ℝ) :
    PrimeWeldLorentzIntegralTraceDescent a ↔ a = 0 := by
  constructor
  · exact eq_zero_of_primeWeldLorentzIntegralTraceDescent
  · rintro rfl x hx
    refine ⟨2, ?_⟩
    rw [trace_lorentzBoost]
    norm_num

/-- A common integral Lorentz lattice frame forces neutral horizontal grade. -/
theorem eq_zero_of_primeWeldIntegralLorentzLatticeFrame
    {a : ℝ} (F : PrimeWeldIntegralLorentzLatticeFrame a) : a = 0 :=
  eq_zero_of_primeWeldLorentzIntegralTraceDescent F.traceDescent

/-- Canonical common integral frame at neutral grade. -/
def primeWeldIntegralLorentzLatticeFrameZero :
    PrimeWeldIntegralLorentzLatticeFrame 0 where
  basis := 1
  coordinates := fun _ _ => 1
  intertwine := by
    intro x hx
    simp [lorentzBoost_zero]

/-- **Common-lattice classification.** The dense prime-weld Lorentz action admits one rank-two
integral frame exactly at neutral horizontal grade. -/
theorem primeWeldIntegralLorentzLatticeFrame_nonempty_iff (a : ℝ) :
    Nonempty (PrimeWeldIntegralLorentzLatticeFrame a) ↔ a = 0 := by
  constructor
  · rintro ⟨F⟩
    exact eq_zero_of_primeWeldIntegralLorentzLatticeFrame F
  · rintro rfl
    exact ⟨primeWeldIntegralLorentzLatticeFrameZero⟩

end

end RHTower
