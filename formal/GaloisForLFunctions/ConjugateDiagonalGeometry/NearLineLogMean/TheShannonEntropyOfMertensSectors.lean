import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.ThePowerSpectrumOfReciprocalMertensMass
import GaloisForLFunctions.LogarithmicChowla.FiniteEntropy
import Mathlib.Algebra.Order.Chebyshev

/-!
# Shannon entropy of reciprocal Mertens weights and their sectors

A sector records only a label of an integer in the section. The
Shannon sector entropy of Perez-Obiol, Boshier, Amico and Polo is the entropy of the
resulting label probabilities. For the reciprocal Mertens law every
equipartition loses a sublogarithmic amount from its maximal label
entropy, uniformly over all choices and numbers of sectors.
-/
noncomputable section
open Finset Filter Topology
open _root_.RHTower GaloisForLFunctions.LogarithmicChowla
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

def mertensPrefixLaw (N : ℕ) (i : Fin N) :=
  reciprocalMertensWeight (i.val+1)/mertensAbelMass N

private theorem law_nonneg (N : ℕ) (i : Fin N) : 0 ≤ mertensPrefixLaw N i :=
  div_nonneg (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (mertens_abel_mass_nonneg N)

private theorem law_power_sum (q : ℝ) (N : ℕ) :
    (∑ i : Fin N,(mertensPrefixLaw N i)^q) =
      reciprocalMertensMoment q N/(mertensAbelMass N)^q := by
  calc _ = ∑ j ∈ range N,(reciprocalMertensWeight (j+1)/mertensAbelMass N)^q :=
         Fin.sum_univ_eq_sum_range (fun j => (reciprocalMertensWeight (j+1)/mertensAbelMass N)^q) N
       _ = (∑ j ∈ range N,(reciprocalMertensWeight (j+1))^q)/(mertensAbelMass N)^q := by
         rw [sum_div]
         refine sum_congr rfl fun j _ => ?_
         have hw : 0 ≤ reciprocalMertensWeight (j+1) := div_nonneg
           (norm_nonneg (mobiusMertensPartialSum (j+1))) (Nat.cast_nonneg (α:=ℝ) (j+1))
         exact Real.div_rpow hw (mertens_abel_mass_nonneg N) q
       _ = _ := by rw [reciprocalMertensMoment,_root_.RHTower.sum_Icc_eq_sum_range_shift]

private theorem law_total {N : ℕ} (hn : 1 ≤ N) : ∑ i, mertensPrefixLaw N i=1 := by
  have h := law_power_sum 1 N
  have hm := zero_lt_one.trans_le (reciprocal_mertens_moment_one_le 1 hn)
  rw [reciprocal_mertens_first_moment] at hm
  simpa only [Real.rpow_one,reciprocal_mertens_first_moment,div_self hm.ne'] using h

private theorem positive_collision_mass {α : Type*} [Fintype α] (p : α → ℝ)
    (h1 : ∑ i,p i=1) : 0 < ∑ i,(p i)^2 := by
  by_contra! h
  have hz (i : α) : (p i)^2 ≤ 0 :=
    (single_le_sum (fun j _ => sq_nonneg (p j)) (mem_univ i)).trans h
  have hzero (i : α) : p i=0 := sq_eq_zero_iff.mp (le_antisymm (hz i) (sq_nonneg _))
  simp [hzero] at h1

private theorem entropy_lower_from_collision {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i,p i=1) :
    -Real.log (∑ i,(p i)^2) ≤ ent p := by
  let C := ∑ i,(p i)^2
  have hc : 0 < C := positive_collision_mass p h1
  have row (i : α) : p i*Real.log (p i)-p i*Real.log C ≤ (p i)^2/C-p i := by
    rcases (hp i).eq_or_lt with hi|hi
    · simp [←hi]
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hi hc)) hi.le
    rw [Real.log_div hi.ne' hc.ne'] at h
    calc _ = p i*(Real.log (p i)-Real.log C) := by ring
         _ ≤ p i*(p i/C-1) := h
         _ = _ := by ring
  have h := sum_le_sum (s:=univ) (fun i _ => row i)
  rw [sum_sub_distrib,sum_sub_distrib,←sum_mul,←sum_div,h1,one_mul] at h
  change _ ≤ C/C-1 at h
  rw [div_self hc.ne',sub_self] at h
  rw [ent_eq]
  linarith only [h]

/-- Reciprocal Mertens mass has full Shannon dimension, including if
some nontrivial zeta zeros lie off the critical line. -/
theorem mertens_shannon_dimension :
    Tendsto (fun N : ℕ => ent (mertensPrefixLaw N)/Real.log ((N:ℝ)+1)) atTop (𝓝 1) := by
  have hl := (low_reciprocal_mertens_moment_order (q:=2) (by norm_num) le_rfl).neg
  norm_num at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with N hn
    have h := entropy_lower_from_collision (law_nonneg N) (law_total hn)
    have hc := law_power_sum 2 N
    simp only [Real.rpow_two] at hc
    rw [hc] at h
    have hp : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by linarith only [Nat.cast_nonneg (α:=ℝ) N])
    simpa only [Pi.neg_apply,neg_div,Real.rpow_two] using div_le_div_of_nonneg_right h hp
  · filter_upwards [eventually_ge_atTop 1] with N hn
    have h := ent_le_log_card (law_nonneg N) (law_total hn)
    rw [Fintype.card_fin] at h
    have hp : 0 < (N:ℝ) := Nat.cast_pos.mpr hn
    exact (div_le_one (Real.log_pos (by linarith only [hp]))).mpr
      (h.trans (Real.log_le_log hp (by linarith only [])))

private theorem sector_collision {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → ℝ) (F : α → β) (K : ℕ) (hK : ∀ b, (univ.filter (fun i => F i=b)).card ≤ K) :
    (∑ b,(push F p b)^2) ≤ (K:ℝ)*∑ i,(p i)^2 := by
  classical
  have row (b : β) : (push F p b)^2 ≤ (K:ℝ)*push F (fun i => (p i)^2) b :=
    (sq_sum_le_card_mul_sum_sq (s:=univ.filter (fun i => F i=b)) (f:=p)).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hK b)) (sum_nonneg fun i _ => sq_nonneg (p i)))
  have h := sum_le_sum (s:=univ) (fun b _ => row b)
  rwa [←mul_sum,sum_push] at h

/-- All balanced sector maps obey a common entropy-deficit estimate.
The labels and their number may vary with the cutoff. -/
theorem every_equipartition_of_mertens_mass_has_full_sector_entropy (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (M K : ℕ), M*K=N → ∀ (F : Fin N → Fin M),
      (∀ b, (univ.filter (fun i => F i=b)).card ≤ K) →
      0 ≤ Real.log M-ent (push F (mertensPrefixLaw N)) ∧
      Real.log M-ent (push F (mertensPrefixLaw N)) ≤ ε*Real.log ((N:ℝ)+1) := by
  have hs := low_reciprocal_mertens_moment_order (q:=2) (by norm_num) le_rfl
  have hev := hs.eventually_lt_const (show 1-(2:ℝ)< -1+ε by linarith only [hε])
  filter_upwards [hev,eventually_ge_atTop 1] with N h hn M K he F hf
  have hp : 0 < (N:ℝ) := Nat.cast_pos.mpr hn
  have hx := Real.log_pos (by linarith only [hp] : 1 < (N:ℝ)+1)
  have hk : 0 < (K:ℝ) := Nat.cast_pos.mpr (by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at he; omega)
  have hm : 0 < (M:ℝ) := Nat.cast_pos.mpr (by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at he; omega)
  let p := mertensPrefixLaw N
  have hg := push_nonneg F (law_nonneg N)
  have h1 : ∑ b,push F p b=1 := (sum_push F p).trans (law_total hn)
  have hl := entropy_lower_from_collision hg h1
  have hu := ent_le_log_card hg h1
  rw [Fintype.card_fin] at hu
  refine ⟨sub_nonneg.mpr hu,?_⟩
  have hspos := positive_collision_mass (push F p) h1
  have hc := sector_collision p F K hf
  have hpos := hspos.trans_le hc
  have hpos' := pos_of_mul_pos_right hpos hk.le
  have hlog := Real.log_le_log hspos hc
  rw [Real.log_mul hk.ne' hpos'.ne'] at hlog
  have heq : ∑ i,(p i)^2 = reciprocalMertensMoment 2 N/(mertensAbelMass N)^(2:ℝ) := by
    simpa only [Real.rpow_two,p] using law_power_sum 2 N
  rw [heq] at hlog
  have hMK : (M:ℝ)*K=N := by exact_mod_cast he
  have hsumlog : Real.log M+Real.log K=Real.log N := by rw [←Real.log_mul hm.ne' hk.ne',hMK]
  have hNlog := Real.log_le_log hp (show (N:ℝ) ≤ N+1 by linarith only [])
  have hsmall := (div_lt_iff₀ hx).mp h
  linarith only [hlog,hl,hsumlog,hNlog,hsmall]

/-- For any product labelling of the samples, randomizing the internal
label within each sector costs sublogarithmic relative entropy. This
is the deficit in the conditional part of the sector entropy split. -/
theorem mertens_information_within_balanced_sectors (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (M K : ℕ) (e : Fin N ≃ Fin M × Fin K),
      let p := push e (mertensPrefixLaw N)
      let uniformWithin := fun t : Fin M × Fin K => push Prod.fst p t.1 / K
      0 ≤ kl p uniformWithin ∧ kl p uniformWithin ≤ ε*Real.log ((N:ℝ)+1) := by
  have hlim := mertens_shannon_dimension.eventually_const_lt
    (show 1-ε < (1:ℝ) by linarith only [hε])
  filter_upwards [hlim,eventually_ge_atTop 1] with N hnear hn M K e
  have he : M*K=N := by simpa only [Fintype.card_fin,Fintype.card_prod] using (Fintype.card_congr e).symm
  have hk : 0<K := Nat.pos_of_ne_zero (fun hz => by rw [hz,mul_zero] at he; omega)
  have hm : 0<M := Nat.pos_of_ne_zero (fun hz => by rw [hz,zero_mul] at he; omega)
  letI : NeZero K := ⟨Nat.ne_of_gt hk⟩
  let p := push e (mertensPrefixLaw N)
  let q := push Prod.fst p
  let ν := fun t : Fin M × Fin K => q t.1 / K
  change 0 ≤ kl p ν ∧ kl p ν ≤ _
  have hp : ∀ t, 0 ≤ p t := push_nonneg e (law_nonneg N)
  have hq : ∀ b, 0 ≤ q b := push_nonneg Prod.fst hp
  have h1 : ∑ t,p t=1 := (sum_push e _).trans (law_total hn)
  have hq1 : ∑ b,q b=1 := (sum_push Prod.fst p).trans h1
  have hk' : 0 < (K:ℝ) := Nat.cast_pos.mpr hk
  have hν : ∑ t,ν t=1 := by
    simp only [ν,Fintype.sum_prod_type,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    convert hq1 using 1
    exact sum_congr rfl fun b _ => by field_simp
  have hpos (t : Fin M × Fin K) (ht : 0 < p t) : 0 < ν t :=
    div_pos (ht.trans_le (le_push Prod.fst hp t)) hk'
  have hnon := sum_sub_sum_le_kl hp (fun t => div_nonneg (hq t.1) hk'.le) hpos
  change (∑ t,p t)-(∑ t,ν t) ≤ kl p ν at hnon
  rw [h1,hν,sub_self] at hnon
  refine ⟨hnon,?_⟩
  have hid := kl_prod_uniform hp
  simp only [Fintype.card_fin] at hid
  change kl p ν = ent q + Real.log K * (∑ t,p t) - ent p at hid
  rw [h1,mul_one] at hid
  have hcap := ent_le_log_card hq hq1
  rw [Fintype.card_fin] at hcap
  have he' : (M:ℝ)*K=N := by exact_mod_cast he
  have hlog : Real.log M + Real.log K = Real.log N := by
    rw [←Real.log_mul (Nat.cast_ne_zero.mpr hm.ne') hk'.ne',he']
  have hn' : 0 < (N:ℝ) := Nat.cast_pos.mpr hn
  have hl := (lt_div_iff₀ (Real.log_pos (by linarith only [hn'] : 1 < (N:ℝ)+1))).mp hnear
  rw [sub_mul,one_mul] at hl
  have hsame : ent p=ent (mertensPrefixLaw N) := ent_push_equiv e _
  have hlog' := Real.log_le_log hn' (le_add_of_nonneg_right zero_le_one)
  linarith only [hid,hcap,hlog,hlog',hl,hsame]

#print axioms mertens_shannon_dimension
#print axioms every_equipartition_of_mertens_mass_has_full_sector_entropy
#print axioms mertens_information_within_balanced_sectors
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
