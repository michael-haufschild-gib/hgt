import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.LabelReflection
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.ReferenceAmplitude
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Radix
import GaloisForLFunctions.CountingHolography.ModularConjugationIsNotThePartnerInvolution
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting

/-! # Particle-hole conjugation detects the global isometry line in every finite factor -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing CountingHolography

variable {ι κ : Type*} [Fintype ι]

/-- Product pairing determines both the top state and the exchange of every pair of levels. -/
theorem unique_particle_hole_pair {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) :
    ∃! v : ι × Equiv.Perm ι, ∀ i, a i*a (v.2 i) = a v.1 := by
  obtain ⟨m,R,hr,_⟩ := finite_label_reflection h
  refine ⟨(m,R),hr,?_⟩
  rintro ⟨n,Q⟩ hq
  obtain ⟨u,_⟩ := h.2 1
  have ha : Function.Injective a := fun i j he =>
    congrArg Prod.fst (h.1 (a₁ := (i,u.2)) (a₂ := (j,u.2)) (congrArg (· * b u.2) he))
  obtain ⟨_,_,hu⟩ := unique_divisibility_top h
  have hn := hu n (fun i => ⟨a (Q i),(hq i).symm⟩)
  have hm := hu m (fun i => ⟨a (R i),(hr i).symm⟩)
  have hnm := hn.trans hm.symm
  apply Prod.ext hnm
  apply Equiv.ext
  intro i
  exact ha (mul_left_cancel ((hq i).trans ((congrArg a hnm).trans (hr i).symm)))

/-- Exchange paired energy states and conjugate every amplitude. -/
def energyConjugation (R : Equiv.Perm ι) (hR : Function.Involutive R) :
    AntiunitaryInvol (EuclideanSpace ℂ ι) where
  toFun f := WithLp.toLp 2 (fun i => (starRingEnd ℂ) (f (R i)))
  invol' f := by
    apply PiLp.ext
    intro i
    change (starRingEnd ℂ) ((starRingEnd ℂ) (f (R (R i)))) = f i
    rw [hR,Complex.conj_conj]
  map_add' f g := by
    apply PiLp.ext
    intro i
    exact map_add _ (f (R i)) (g (R i))
  map_smul' c f := by
    apply PiLp.ext
    intro i
    exact map_mul _ c (f (R i))
  inner_map' f g := by
    change (∑ i, inner ℂ ((starRingEnd ℂ) (f (R i))) ((starRingEnd ℂ) (g (R i)))) = ∑ i, inner ℂ (g i) (f i)
    rw [← Equiv.sum_comp R (fun i => inner ℂ (g i) (f i))]
    apply Finset.sum_congr rfl
    intro i _
    simp [RCLike.inner_apply,mul_comm]

/-- Complex heat amplitudes expressed in units of the equilibrium boundary amplitudes. -/
def relativeState (a : ι → ℕ+) (s : ℂ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => relativeCoefficient s (a i))

private theorem relative_one (s : ℂ) : relativeCoefficient s 1 = 1 := by
  simp [relativeCoefficient,heat,energy]

omit [Fintype ι] in
private theorem coefficient_duality {a : ι → ℕ+} {m : ι} {R : Equiv.Perm ι}
    (h : ∀ i, a i*a (R i) = a m) (s : ℂ) (i : ι) :
    (starRingEnd ℂ) (relativeCoefficient s (a (R i))) =
      relativeCoefficient ((starRingEnd ℂ) s) (a m)*relativeCoefficient (1-(starRingEnd ℂ) s) (a i) := by
  let w := (starRingEnd ℂ) s - 1/2
  have h₂ : (starRingEnd ℂ) 2 = 2 := by rw [← one_add_one_eq_two,map_add,map_one]
  have hc : (starRingEnd ℂ) (relativeCoefficient s (a (R i))) = heat w (a (R i)) := by
    simp [relativeCoefficient,heat,w,← Complex.exp_conj,h₂]
  have hn : 1-(starRingEnd ℂ) s-1/2 = -w := by dsimp [w]; ring
  rw [hc,relativeCoefficient,relativeCoefficient,hn,← h i,heat_mul]
  have hu : heat w (a i)*heat (-w) (a i) = 1 := by
    rw [← heat_add,add_neg_cancel]
    simp [heat]
  change heat w (a (R i)) = heat w (a i)*heat w (a (R i))*heat (-w) (a i)
  calc
    _ = heat w (a (R i))*(heat w (a i)*heat (-w) (a i)) := by rw [hu,mul_one]
    _ = _ := by ring

omit [Fintype ι] in
private theorem energy_top_pos [Nontrivial ι] {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b)
    {m : ι} {R : Equiv.Perm ι} (hr : ∀ i, a i*a (R i) = a m) : 0 < energy (a m) := by
  apply Real.log_pos
  have hn : (a m).val ≠ 1 := by
    intro hm
    obtain ⟨j,hj⟩ := exists_ne m
    obtain ⟨v,_⟩ := h.2 1
    have hprod : (a j).val*(a (R j)).val = 1 := (congrArg PNat.val (hr j)).trans hm
    have he : a j = a m := PNat.coe_injective ((Nat.eq_one_of_mul_eq_one_right hprod).trans hm.symm)
    exact hj (congrArg Prod.fst (h.1 (a₁ := (j,v.2)) (a₂ := (m,v.2)) (congrArg (· * b v.2) he)))
  have hp := (a m).pos
  exact_mod_cast (show 1 < (a m).val by omega)

private theorem eigenline_necessary [Nontrivial ι] {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b)
    {m : ι} {R : Equiv.Perm ι} (hr : ∀ i, a i*a (R i) = a m) (hR : Function.Involutive R) (s : ℂ)
    (he : ∃ c : ℂ, energyConjugation R hR (relativeState a s) = c • relativeState a s) : s.re = 1/2 := by
  obtain ⟨c,hc⟩ := he
  let v := factorVacuum h
  have hv : a v = 1 := factorVacuum_label h
  have ht : a (R v) = a m := by simpa only [hv,one_mul] using hr v
  have hc' (i : ι) : (starRingEnd ℂ) (relativeCoefficient s (a (R i))) = c*relativeCoefficient s (a i) :=
    congrArg (fun f : EuclideanSpace ℂ ι => f i) hc
  have hlow := hc' v
  rw [ht,hv,relative_one,mul_one] at hlow
  have htop := hc' (R v)
  rw [hR,hv,relative_one,map_one,ht,← hlow,Complex.conj_mul'] at htop
  have hs : (1:ℝ) = ‖relativeCoefficient s (a m)‖^2 := by exact_mod_cast htop
  have hnorm : ‖relativeCoefficient s (a m)‖ = 1 := by nlinarith only [hs,norm_nonneg (relativeCoefficient s (a m))]
  rw [relativeCoefficient,norm_heat,Real.exp_eq_one_iff] at hnorm
  have hz := neg_eq_zero.mp ((mul_eq_zero.mp hnorm).resolve_right (energy_top_pos h hr).ne')
  rw [Complex.sub_re,show (1/2:ℂ).re = 1/2 by norm_num] at hz
  exact sub_eq_zero.mp hz

/-- An intrinsic antiunitary realizes the reflected parameter. Its invariant heat rays are exactly the globally isometric compositions. -/
theorem particleHole_eigenline_iff_split [Nontrivial ι] {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) :
    ∃ m : ι, ∃ J : AntiunitaryInvol (EuclideanSpace ℂ ι),
      (∀ s : ℂ, J (relativeState a s) =
        relativeCoefficient ((starRingEnd ℂ) s) (a m) • relativeState a (1-(starRingEnd ℂ) s)) ∧
      ∀ s : ℂ, (∃ c : ℂ, J (relativeState a s) = c • relativeState a s) ↔
        ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  obtain ⟨m,R,hr,hR⟩ := finite_label_reflection h
  let J := energyConjugation R hR
  have hJ (s : ℂ) : J (relativeState a s) =
      relativeCoefficient ((starRingEnd ℂ) s) (a m) • relativeState a (1-(starRingEnd ℂ) s) := by
    apply PiLp.ext
    intro i
    exact coefficient_duality hr s i
  refine ⟨m,J,hJ,fun s => ?_⟩
  rw [split_isometric_iff]
  constructor
  · exact eigenline_necessary h hr hR s
  · intro hs
    have hd : 1-(starRingEnd ℂ) s = s := by
      apply Complex.ext
      · simp only [Complex.sub_re,Complex.one_re,Complex.conj_re,hs]
        norm_num
      · simp
    exact ⟨_,hd ▸ hJ s⟩

/-- Every prime and every nontrivial digit length give an unconditional finite detector. -/
theorem prime_digit_particleHole (q : Nat.Primes) (d : ℕ) :
    ∃ J : AntiunitaryInvol (EuclideanSpace ℂ (Fin (d+2))), ∀ s : ℂ,
      (∃ c : ℂ, J (relativeState (fun i : Fin (d+2) => primeRayLabel q i.val) s) =
        c • relativeState (fun i : Fin (d+2) => primeRayLabel q i.val) s) ↔
        ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  let D : ℕ+ := ⟨d+2,by omega⟩
  letI : Nontrivial (Fin D.val) := inferInstanceAs (Nontrivial (Fin (d+2)))
  obtain ⟨_,J,_,hJ⟩ := particleHole_eigenline_iff_split (radix_exact q D)
  exact ⟨J,hJ⟩

#print axioms energyConjugation
#print axioms unique_particle_hole_pair
#print axioms particleHole_eigenline_iff_split
#print axioms prime_digit_particleHole

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
