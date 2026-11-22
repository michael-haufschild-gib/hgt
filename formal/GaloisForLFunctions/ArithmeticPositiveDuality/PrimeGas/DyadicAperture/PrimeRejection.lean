import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.RejectedHeat
import GaloisForLFunctions.SurfaceOfSpecZ.HasseWeilForPairsOfPrimeDegrees
import Mathlib.Data.PNat.Prime

/-!
# Prime insertions in the rejected sector

Prime energy differences are dense. One prime insertion on each copy
rotates a positive neighborhood of the identity into any open rejection
arc. The first reading alone therefore rejects a full-boundary gas.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary

open SampledClocks CopyExchange Set Filter Topology

private def gain (t : ℝ) (p q : ℕ+) := Circle.exp (t*(energy p-energy q))

def insertPrimes (p q : Nat.Primes) (x : Word) : Word :=
  fun b => (cond b q.toPNat p.toPNat)*x b

private theorem inserted_phase (t : ℝ) (p q : Nat.Primes) (x : Word) :
    (binary t).phase () (insertPrimes p q x) = gain t p.toPNat q.toPNat*
      (binary t).phase () x := by
  change Circle.exp (t*(energy (p.toPNat*x false)-energy (q.toPNat*x true))) =
    Circle.exp (t*(energy p.toPNat-energy q.toPNat))*Circle.exp (t*(energy (x false)-energy (x true)))
  rw [← Circle.exp_add,energy_mul,energy_mul]
  congr 1
  ring

private theorem radius_lt_two (θ : Set.Ioo 0 Real.pi) : Real.sqrt (aperture θ.val) < 2 := by
  have hcos := Real.strictAntiOn_cos (show θ.val ∈ Set.Icc 0 Real.pi from ⟨θ.property.1.le,θ.property.2.le⟩)
    (show Real.pi ∈ Set.Icc 0 Real.pi from ⟨Real.pi_pos.le,le_rfl⟩) θ.property.2
  rw [Real.cos_pi] at hcos
  have hp : 0 ≤ aperture θ.val := by unfold aperture; linarith only [Real.cos_le_one θ.val]
  rw [← sq_lt_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 2),Real.sq_sqrt hp]
  unfold aperture
  linarith only [hcos]

private theorem hitting_primes (t : {t : ℝ // t ≠ 0}) (θ : Set.Ioo 0 Real.pi) :
    ∃ p q : Nat.Primes, Real.sqrt (aperture θ.val) < dist
      (gain t.val p.toPNat q.toPNat) 1 := by
  let U : Set ℝ := {g | Real.sqrt (aperture θ.val) < dist (Circle.exp (t.val*g)) 1}
  have ho : IsOpen U := isOpen_lt continuous_const ((Circle.exp.continuous.comp (continuous_const.mul continuous_id)).dist continuous_const)
  have hcenter : Real.pi/t.val ∈ U := by
    change _ < dist (Circle.exp (t.val*(Real.pi/t.val))) 1
    rw [show t.val*(Real.pi/t.val) = Real.pi by field_simp [t.property],exp_pi]
    change _ < dist (-1:ℂ) 1
    rw [show dist (-1:ℂ) 1 = 2 by norm_num [dist_eq_norm]]
    exact radius_lt_two θ
  obtain ⟨δ,hδ,hi⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hcenter)
  obtain ⟨g,hg,p,q,hp,hq,he⟩ := Metric.dense_iff.mp SurfaceOfSpecZ.dense_primeLogRatios _ δ hδ
  refine ⟨⟨p,hp⟩,⟨q,hq⟩,?_⟩
  change Real.log (p:ℝ)-Real.log (q:ℝ) ∈ U
  rw [← he]
  exact hi hg

def firstRejection (t θ : ℝ) (x : Word) := Real.sqrt (aperture θ) ≤ dist ((binary t).phase () x) 1

/-- The two prime creations move an entire first-readout neighborhood beyond the hardware cutoff. -/
theorem prime_insertion (t : {t : ℝ // t ≠ 0}) (θ : Set.Ioo 0 Real.pi) :
    ∃ (p q : Nat.Primes) (δ : {u : ℝ // 0 < u}), ∀ x : Word, (binary t.val).Prefix δ.val 1 x →
      firstRejection t.val θ.val (insertPrimes p q x) := by
  obtain ⟨p,q,hpq⟩ := hitting_primes t θ
  let v := gain t.val p.toPNat q.toPNat
  refine ⟨p,q,⟨dist v 1-Real.sqrt (aperture θ.val),sub_pos.mpr hpq⟩,?_⟩
  intro x hx
  let w := (binary t.val).phase () x
  have hw : dist w 1 < dist v 1-Real.sqrt (aperture θ.val) := by
    simpa only [Network.multiple_phase,Fin.val_zero,pow_zero,pow_one,w] using hx (0 : Fin 1) ()
  have hi : dist v (v*w) = dist w 1 := by
    rw [dist_comm v]
    change dist ((v:ℂ)*(w:ℂ)) v = dist (w:ℂ) 1
    rw [dist_eq_norm,dist_eq_norm,show (v:ℂ)*(w:ℂ)-v = (v:ℂ)*((w:ℂ)-1) by ring,
      norm_mul,Circle.norm_coe,one_mul]
  have ht := dist_triangle v (v*w) 1
  rw [hi] at ht
  unfold firstRejection
  rw [inserted_phase]
  change _ ≤ dist (v*w) 1
  linarith only [ht,hw]

theorem first_rejected_heat (t : {t : ℝ // t ≠ 0}) (θ : Set.Ioo 0 Real.pi) (s : ℂ) :
    HasSectorHeat (firstRejection t.val θ.val) s ↔ 1 < s.re := by
  constructor
  · intro h
    obtain ⟨p,q,δ,inc⟩ := prime_insertion t θ
    let G := binary t.val
    let f (x : {x // G.Prefix δ.val 1 x}) : {x // firstRejection t.val θ.val x} := ⟨insertPrimes p q x.val,inc _ x.property⟩
    have hi : Function.Injective f := by
      intro x y he
      apply Subtype.ext
      funext b
      have hb := congrArg (fun u : {x // firstRejection t.val θ.val x} => u.val b) he
      change (cond b q.toPNat p.toPNat)*x.val b = (cond b q.toPNat p.toPNat)*y.val b at hb
      exact mul_left_cancel hb
    let C := ‖heat s p.toPNat‖*‖heat s q.toPNat‖
    have hC : 0 < C := mul_pos (norm_pos_iff.mpr (Complex.exp_ne_zero _)) (norm_pos_iff.mpr (Complex.exp_ne_zero _))
    have hs := ((sectorHeat_iff _ _).mp h).comp_injective (i := f) hi
    have hw : Summable fun x : {x // G.Prefix δ.val 1 x} => C*‖wordHeat s x.val‖ := by
      refine hs.congr fun x => ?_
      change ‖wordHeat s (insertPrimes p q x.val)‖ = _
      simp only [wordHeat,Fintype.prod_bool,insertPrimes,cond_true,cond_false,heat_mul,norm_mul,C]
      ring
    apply (G.prefix_heat_iff δ 1 s).mp
    apply (sectorHeat_iff _ _).mpr
    simpa only [← mul_assoc,inv_mul_cancel₀ hC.ne',one_mul] using hw.mul_left C⁻¹
  · exact fun h => restrict_heat s (fun _ _ => trivial) ((full_heat s).mpr h)

theorem proper_rejected_heat (t : {t : ℝ // t ≠ 0}) (θ : Set.Ioo 0 Real.pi) (s : ℂ) :
    HasSectorHeat (fun x => ¬measured t.val θ.val x) s ↔ 1 < s.re := by
  constructor
  · intro h
    apply (first_rejected_heat t θ s).mp
    apply restrict_heat s _ h
    intro x hx hp
    have h₀ := hp 0 ()
    rw [Network.multiple_phase,pow_zero,pow_one] at h₀
    exact (not_lt.mpr hx) h₀
  · exact fun h => restrict_heat s (fun _ _ => trivial) ((full_heat s).mpr h)

#print axioms prime_insertion
#print axioms first_rejected_heat
#print axioms proper_rejected_heat

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary
