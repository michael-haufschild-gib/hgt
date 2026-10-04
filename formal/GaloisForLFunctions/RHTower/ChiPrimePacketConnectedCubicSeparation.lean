import GaloisForLFunctions.RHTower.ChiPrimePacketCubicMoment
import GaloisForLFunctions.RHTower.BourgainGaussianFourier
import GaloisForLFunctions.HTGeometry.LogarithmicSpacing
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-!
# Connected quadratic mixing with divergent signed prime cubic

Source PNT supplies dense prime packets in a coherent short interval. Independent
Bernoulli thinning controls every nonzero difference fibre simultaneously: each
shift graph splits into two matchings, so a finite Hoeffding union bound retains
many primes while making every fibre small relative to the retained cardinality.

A global logarithmic Gaussian bound, with its complete integer tail, turns that
fibre estimate into uniform connected pair decay for all real twists and all
height centres. The exact diagonal packet remains subtracted even near twist one.
The same selected packet retains the source's positive signed physical cubic,
with both repeated-prime contraction families removed and all kernel errors paid.

The final unconditional theorem constructs unit-energy actual prime packets with
connected average at most C/K and signed noncontracting cubic at least T*K^2/1024.
Thus the entire connected quadratic statistic cannot alone control the cubic.
This is a subpacket construction, not an estimate of the full Gaussian prime band
and not an RH proof or falsification.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter Set Complex
open GaloisForLFunctions.RHTower
open scoped Topology NNReal
namespace RHTower.PrimePacketThinning

private def law (p : unitInterval) : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p)

private instance (p : unitInterval) : IsProbabilityMeasure (law p) := by
  unfold law
  infer_instance

private def bit (b : Bool) : ℝ := if b = true then 1 else 0
private def pick (n : ℕ) (ω : ℕ → Bool) : ℝ := bit (ω n)

private theorem measurable_bit : Measurable bit := by
  exact measurable_of_finite _

private theorem measurable_pick (n : ℕ) : Measurable (pick n) :=
  measurable_bit.comp (measurable_pi_apply n)

private theorem pick_mem (n : ℕ) (ω : ℕ → Bool) : pick n ω ∈ Icc (0 : ℝ) 1 := by
  simp only [pick,bit]
  split_ifs <;> norm_num

private theorem indep_pick (p : unitInterval) : iIndepFun pick (law p) :=
  iIndepFun_infinitePi (P := fun _ : ℕ => bernoulliMeasure true false p)
    (X := fun _ => bit) (fun _ => measurable_bit)

private theorem integral_pick (p : unitInterval) (n : ℕ) : ∫ ω, pick n ω ∂law p = (p : ℝ) := by
  have hmap : (law p).map (fun ω : ℕ → Bool => ω n) = bernoulliMeasure true false p :=
    Measure.infinitePi_map_eval _ n
  have hi := integral_map (μ := law p) (φ := fun ω : ℕ → Bool => ω n)
    (measurable_pi_apply n).aemeasurable measurable_bit.aestronglyMeasurable
  change (∫ ω, bit (ω n) ∂law p) = _
  rw [← hi,hmap,integral_bernoulliMeasure]
  norm_num [bit]

private theorem integral_edge (p : unitInterval) {a b : ℕ} (hab : a ≠ b) :
    ∫ ω, pick a ω*pick b ω ∂law p = (p : ℝ)^2 := by
  rw [((indep_pick p).indepFun hab).integral_fun_mul_eq_mul_integral
    (measurable_pick a).aestronglyMeasurable (measurable_pick b).aestronglyMeasurable,
    integral_pick,integral_pick]
  ring

private theorem subgaussian_edge (p : unitInterval) {a b : ℕ} (hab : a ≠ b) :
    HasSubgaussianMGF (fun ω => pick a ω*pick b ω-(p : ℝ)^2) 1 (law p) := by
  have hm : Measurable (fun ω => pick a ω*pick b ω) := (measurable_pick a).mul (measurable_pick b)
  have hmem : ∀ᵐ ω ∂law p, pick a ω*pick b ω ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [] with ω
    have ha := pick_mem a ω
    have hb := pick_mem b ω
    exact ⟨mul_nonneg ha.1 hb.1,(mul_le_mul ha.2 hb.2 hb.1 (by norm_num)).trans_eq (by ring)⟩
  have he := integral_edge p hab
  have hi : Integrable (fun ω => pick a ω*pick b ω) (law p) := Integrable.of_mem_Icc 0 1 hm.aemeasurable hmem
  have hcenter : ∫ ω, (pick a ω*pick b ω-(p : ℝ)^2) ∂law p = 0 := by
    rw [integral_sub hi (integrable_const _),integral_const,probReal_univ,one_smul,he,sub_self]
  have hcenter_mem : ∀ᵐ ω ∂law p, pick a ω*pick b ω-(p : ℝ)^2 ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [hmem] with ω hω
    have hp0 := p.property.1
    have hp1 := p.property.2
    constructor <;> nlinarith only [hω.1,hω.2,hp0,hp1,sq_nonneg (p : ℝ)]
  have hg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (hm.sub_const _).aemeasurable hcenter_mem hcenter
  norm_num at hg
  exact hg

private def endpoints (h a : ℕ) : Finset ℕ := {a,a+h}

private theorem indep_edge_sum (p : unitInterval) (h a : ℕ) (s : Finset ℕ)
    (hsep : ∀ b ∈ s, Disjoint (endpoints h a) (endpoints h b)) :
    IndepFun (fun ω => pick a ω*pick (a+h) ω-(p : ℝ)^2)
      (fun ω => ∑ b ∈ s, (pick b ω*pick (b+h) ω-(p : ℝ)^2)) (law p) := by
  let R := s.biUnion (endpoints h)
  have hdis : Disjoint (endpoints h a) R := by
    rw [Finset.disjoint_left]
    intro n hn hnR
    obtain ⟨b,hbs,hnb⟩ := Finset.mem_biUnion.mp hnR
    exact Finset.disjoint_left.mp (hsep b hbs) hn hnb
  have hb (b : s) : (b : ℕ) ∈ R :=
    Finset.mem_biUnion.mpr ⟨b,b.property,by simp [endpoints]⟩
  have hb' (b : s) : (b : ℕ)+h ∈ R :=
    Finset.mem_biUnion.mpr ⟨b,b.property,by simp [endpoints]⟩
  let F : (endpoints h a → ℝ) → ℝ := fun x =>
    x ⟨a,by simp [endpoints]⟩*x ⟨a+h,by simp [endpoints]⟩-(p : ℝ)^2
  let G : (R → ℝ) → ℝ := fun x =>
    ∑ b : s, (x ⟨b,hb b⟩*x ⟨(b : ℕ)+h,hb' b⟩-(p : ℝ)^2)
  have hF : Measurable F := by unfold F; fun_prop
  have hG : Measurable G := by unfold G; fun_prop
  have hi := (indep_pick p).indepFun_finset (endpoints h a) R hdis measurable_pick
  have hc := hi.comp hF hG
  dsimp only [F,G,Function.comp_def] at hc
  convert hc using 1
  ext ω
  exact (Finset.sum_attach s (fun b => pick b ω*pick (b+h) ω-(p : ℝ)^2)).symm

private theorem subgaussian_matching (p : unitInterval) {h : ℕ} (hh : 0 < h)
    (s : Finset ℕ) (hs : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      Disjoint (endpoints h a) (endpoints h b)) :
    HasSubgaussianMGF (fun ω => ∑ a ∈ s, (pick a ω*pick (a+h) ω-(p : ℝ)^2))
      (s.card : ℝ≥0) (law p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hga := subgaussian_edge p (a := a) (b := a+h) (by omega)
    have hgs := ih (fun b hb c hc hbc =>
      hs b (mem_insert_of_mem hb) c (mem_insert_of_mem hc) hbc)
    have hi := indep_edge_sum p h a s (fun b hb =>
      hs a (mem_insert_self _ _) b (mem_insert_of_mem hb) (by aesop))
    simpa [Finset.sum_insert ha,Finset.card_insert_of_notMem ha,add_comm] using
      hga.add_of_indepFun hgs hi

private theorem parity_matching {h : ℕ} (hh : 0 < h) (c : ℕ)
    (s : Finset ℕ) :
    ∀ a ∈ s.filter (fun a => (a/h)%2=c),
      ∀ b ∈ s.filter (fun b => (b/h)%2=c), a ≠ b →
      Disjoint (endpoints h a) (endpoints h b) := by
  intro a ha b hb hab
  have ha' := (mem_filter.mp ha).2
  have hb' := (mem_filter.mp hb).2
  rw [Finset.disjoint_left]
  intro n hn hn'
  simp only [endpoints,Finset.mem_insert,Finset.mem_singleton] at hn hn'
  have had : (a+h)/h = a/h+1 := Nat.add_div_right a hh
  have hbd : (b+h)/h = b/h+1 := Nat.add_div_right b hh
  rcases hn with hn | hn <;> rcases hn' with hn' | hn'
  · omega
  · have he : a = b+h := hn.symm.trans hn'
    rw [he,hbd] at ha'
    omega
  · have he : b = a+h := hn'.symm.trans hn
    rw [he,had] at hb'
    omega
  · omega

private theorem subgaussian_mono {X : (ℕ → Bool) → ℝ} {p : unitInterval}
    {a b : ℝ≥0} (hX : HasSubgaussianMGF X a (law p)) (hab : a ≤ b) :
    HasSubgaussianMGF X b (law p) where
  integrable_exp_mul := hX.integrable_exp_mul
  mgf_le t := (hX.mgf_le t).trans (Real.exp_le_exp.mpr (by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (show (a : ℝ) ≤ b from hab) (sq_nonneg t)) (by norm_num)))

private theorem subgaussian_vertex (p : unitInterval) (n : ℕ) :
    HasSubgaussianMGF (fun ω => pick n ω-(p : ℝ)) 1 (law p) := by
  have hm := (measurable_pick n).sub_const (p : ℝ)
  have hmem : ∀ᵐ ω ∂law p, pick n ω-(p : ℝ) ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [] with ω
    have hi := pick_mem n ω
    exact ⟨by linarith [p.property.2,hi.1],by linarith [p.property.1,hi.2]⟩
  have hi : Integrable (pick n) (law p) := Integrable.of_mem_Icc 0 1
    (measurable_pick n).aemeasurable (ae_of_all _ (pick_mem n))
  have hc : ∫ ω, (pick n ω-(p : ℝ)) ∂law p = 0 := by
    rw [integral_sub hi (integrable_const _),integral_pick,integral_const,
      probReal_univ,one_smul,sub_self]
  have hg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm.aemeasurable hmem hc
  norm_num at hg
  exact hg

private theorem vertex_tail (p : unitInterval) (s : Finset ℕ) (hM : 0 < s.card) :
    (law p).real {ω | (s.card : ℝ)*(p : ℝ)/2 ≤
      ∑ a ∈ s, ((p : ℝ)-pick a ω)} ≤
      Real.exp (-(s.card : ℝ)*(p : ℝ)^4/8) := by
  have hi : iIndepFun (fun n ω => (p : ℝ)-pick n ω) (law p) := by
    simpa [Function.comp_def] using (indep_pick p).comp
      (fun (_ : ℕ) (x : ℝ) => (p : ℝ)-x) (fun _ => by fun_prop)
  have hg : ∀ n ∈ s, HasSubgaussianMGF (fun ω => (p : ℝ)-pick n ω) 1 (law p) := by
    intro n _
    convert (subgaussian_vertex p n).neg using 1
    ext ω
    simp
  have ht := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hi hg
    (ε := (s.card : ℝ)*(p : ℝ)/2) (by exact div_nonneg (mul_nonneg (by positivity) p.property.1) (by norm_num))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one,NNReal.coe_natCast] at ht
  refine ht.trans (Real.exp_le_exp.mpr ?_)
  have hMr : (0 : ℝ) < s.card := by exact_mod_cast hM
  have he : -((s.card : ℝ)*(p : ℝ)/2)^2/(2*(s.card : ℝ)) =
      -(s.card : ℝ)*(p : ℝ)^2/8 := by
    field_simp
    ring
  rw [he]
  have hp := p.property
  have hp2 : (p : ℝ)^2 ≤ 1 := by nlinarith [hp.1,hp.2]
  have hp4 : (p : ℝ)^4 ≤ (p : ℝ)^2 := by nlinarith [sq_nonneg (p : ℝ)]
  nlinarith

private theorem matching_tail (p : unitInterval) {h : ℕ} (hh : 0 < h)
    (s t : Finset ℕ) (hst : t ⊆ s) (hM : 0 < s.card)
    (ht : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → Disjoint (endpoints h a) (endpoints h b)) :
    (law p).real {ω | (s.card : ℝ)*(p : ℝ)^2 ≤
      ∑ a ∈ t, (pick a ω*pick (a+h) ω-(p : ℝ)^2)} ≤
      Real.exp (-(s.card : ℝ)*(p : ℝ)^4/8) := by
  have hg := subgaussian_mono (subgaussian_matching p hh t ht)
    (show (t.card : ℝ≥0) ≤ s.card from by exact_mod_cast Finset.card_le_card hst)
  have htail := hg.measure_ge_le (ε := (s.card : ℝ)*(p : ℝ)^2) (by positivity)
  refine htail.trans (Real.exp_le_exp.mpr ?_)
  have hMr : (0 : ℝ) < s.card := by exact_mod_cast hM
  have he : -((s.card : ℝ)*(p : ℝ)^2)^2/(2*(s.card : ℝ)) =
      -(s.card : ℝ)*(p : ℝ)^4/2 := by field_simp
  simp only [NNReal.coe_natCast]
  rw [he]
  have hp4 : 0 ≤ (s.card : ℝ)*(p : ℝ)^4 := by positivity
  linarith

private theorem exists_good_sample (p : unitInterval) (s : Finset ℕ) (H : ℕ)
    (hM : 0 < s.card)
    (hsmall : (1+2*(H : ℝ))*Real.exp (-(s.card : ℝ)*(p : ℝ)^4/8) < 1) :
    ∃ ω : ℕ → Bool,
      (s.card : ℝ)*(p : ℝ)/2 < ∑ a ∈ s, pick a ω ∧
      ∀ h ∈ Finset.Icc 1 H, ∀ c ∈ Finset.range 2,
        ∑ a ∈ s.filter (fun a => (a/h)%2=c), pick a ω*pick (a+h) ω <
          2*(s.card : ℝ)*(p : ℝ)^2 := by
  let E := Real.exp (-(s.card : ℝ)*(p : ℝ)^4/8)
  let V : Set (ℕ → Bool) := {ω | (s.card : ℝ)*(p : ℝ)/2 ≤
      ∑ a ∈ s, ((p : ℝ)-pick a ω)}
  let B : ℕ × ℕ → Set (ℕ → Bool) := fun j =>
    {ω | (s.card : ℝ)*(p : ℝ)^2 ≤
      ∑ a ∈ s.filter (fun a => (a/j.1)%2=j.2),
        (pick a ω*pick (a+j.1) ω-(p : ℝ)^2)}
  let J := (Finset.Icc 1 H) ×ˢ Finset.range 2
  let U := V ∪ ⋃ j ∈ J, B j
  have hV : (law p).real V ≤ E := vertex_tail p s hM
  have hB (j : ℕ × ℕ) (hj : j ∈ J) : (law p).real (B j) ≤ E := by
    have hj' := Finset.mem_product.mp hj
    exact matching_tail p (by have := (Finset.mem_Icc.mp hj'.1).1; omega)
      s _ (Finset.filter_subset _ _) hM
      (parity_matching (by have := (Finset.mem_Icc.mp hj'.1).1; omega) j.2 s)
  have hU : (law p).real U < 1 := by
    calc
      (law p).real U ≤ (law p).real V+(law p).real (⋃ j ∈ J, B j) :=
        measureReal_union_le _ _
      _ ≤ E+∑ j ∈ J, (law p).real (B j) :=
        add_le_add hV (measureReal_biUnion_finset_le _ _)
      _ ≤ E+∑ _j ∈ J, E := add_le_add_right (Finset.sum_le_sum hB) _
      _ = (1+2*(H : ℝ))*E := by simp [J,Nat.card_Icc]; ring
      _ < 1 := hsmall
  have hex : ∃ ω : ℕ → Bool, ω ∉ U := by
    by_contra hn
    have heq : U = Set.univ := Set.eq_univ_of_forall (by simpa using hn)
    rw [heq,probReal_univ] at hU
    exact lt_irrefl _ hU
  obtain ⟨ω,hω⟩ := hex
  have hω' : ω ∉ V ∧ ∀ j ∈ J, ω ∉ B j := by simpa [U] using hω
  refine ⟨ω,?_,?_⟩
  · have hv : (∑ a ∈ s, ((p : ℝ)-pick a ω)) < (s.card : ℝ)*(p : ℝ)/2 :=
      lt_of_not_ge hω'.1
    simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul] at hv
    linarith
  · intro h hh c hc
    have hb := hω'.2 (h,c) (Finset.mem_product.mpr ⟨hh,hc⟩)
    change ¬ (s.card : ℝ)*(p : ℝ)^2 ≤ _ at hb
    have hb' := lt_of_not_ge hb
    simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul] at hb'
    have ht : ((s.filter (fun a => (a/h)%2=c)).card : ℝ) ≤ s.card := by
      exact_mod_cast Finset.card_filter_le s _
    nlinarith [sq_nonneg (p : ℝ)]

private theorem parity_sum (s : Finset ℕ) (h : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ s, f a) = (∑ a ∈ s.filter (fun a => (a/h)%2=0), f a)+
      (∑ a ∈ s.filter (fun a => (a/h)%2=1), f a) := by
  rw [Finset.sum_filter,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hm : (a/h)%2=0 ∨ (a/h)%2=1 := by omega
  rcases hm with hm | hm <;> simp [hm]

/-- Simultaneous thinning of every positive difference fibre in a finite range. -/
private theorem exists_thinning (p : unitInterval) (s : Finset ℕ) (H : ℕ)
    (hM : 0 < s.card)
    (hsmall : (1+2*(H : ℝ))*Real.exp (-(s.card : ℝ)*(p : ℝ)^4/8) < 1) :
    ∃ S : Finset ℕ, S ⊆ s ∧ (s.card : ℝ)*(p : ℝ)/2 < S.card ∧
      ∀ h ∈ Finset.Icc 1 H,
        ((S.filter (fun a => a+h ∈ S)).card : ℝ) < 4*(s.card : ℝ)*(p : ℝ)^2 := by
  obtain ⟨ω,hv,he⟩ := exists_good_sample p s H hM hsmall
  let S := s.filter (fun a => ω a=true)
  have hcard : (S.card : ℝ) = ∑ a ∈ s, pick a ω := by
    rw [show S = s.filter (fun a => ω a=true) from rfl,Finset.card_filter]
    simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,pick,bit]
  refine ⟨S,Finset.filter_subset _ _,by rwa [hcard],?_⟩
  intro h hh
  have hc : ((S.filter (fun a => a+h ∈ S)).card : ℝ) ≤
      ∑ a ∈ s, pick a ω*pick (a+h) ω := by
    rw [Finset.card_filter]
    simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [show S = s.filter (fun a => ω a=true) from rfl,Finset.sum_filter]
    apply Finset.sum_le_sum
    intro a ha
    simp only [pick,bit,Finset.mem_filter]
    split_ifs <;> simp_all
  have h0 := he h hh 0 (by simp)
  have h1 := he h hh 1 (by simp)
  rw [parity_sum s h (fun a => pick a ω*pick (a+h) ω)] at hc
  linarith

private theorem failure_limit :
    Tendsto (fun K : ℕ => (1+2*(K : ℝ)^32)*Real.exp (-(K : ℝ)/8)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun K : ℕ => Real.exp (-(K : ℝ)/8)) atTop (𝓝 0) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1/8) (by norm_num)).comp
      tendsto_natCast_atTop_atTop using 1
    ext K
    simp only [Function.comp_apply,Real.rpow_zero,one_mul]
    congr 1
    ring
  have h32 : Tendsto (fun K : ℕ => (K : ℝ)^32*Real.exp (-(K : ℝ)/8)) atTop (𝓝 0) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 32 (1/8)
      (by norm_num)).comp tendsto_natCast_atTop_atTop using 1
    ext K
    simp only [Function.comp_apply]
    rw [show (32 : ℝ) = (32 : ℕ) by norm_num,Real.rpow_natCast]
    congr 2
    ring
  convert h0.add (h32.const_mul 2) using 1
  · ext K; ring
  · norm_num

/-- Prime packets with simultaneously sparse nonzero difference fibres. -/
theorem eventually_exists_thin_prime_packet :
    ∀ᶠ K : ℕ in atTop, ∃ (N : ℕ) (S : Finset ℕ),
      64*K^64 ≤ N ∧ N ≤ 128*K^64 ∧ (K : ℝ)^23/2 < S.card ∧
      (∀ p ∈ S, p.Prime ∧ N ≤ p ∧ p ≤ N+K^32) ∧
      ∀ h ∈ Finset.Icc 1 (K^32),
        ((S.filter (fun a => a+h ∈ S)).card : ℝ) < 8*(S.card : ℝ)/(K : ℝ) := by
  have hd : ∀ᶠ K : ℕ in atTop, ∃ (N : ℕ) (s : Finset ℕ),
      64*K^64 ≤ N ∧ N ≤ 128*K^64 ∧ K^24 ≤ s.card ∧
      (∀ p ∈ s, p.Prime ∧ N ≤ p ∧ p ≤ N+K^32) := by
    have hh := (tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)).eventually
      RHTower.eventually_exists_dense_prime_packet
    simpa only [← pow_mul] using hh
  filter_upwards [hd,failure_limit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (2 : ℕ)] with K hd hsmall hK
  obtain ⟨N,s,hNlo,hNhi,hM,hprime⟩ := hd
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  have hK1 : (1 : ℝ) ≤ K := by linarith
  let p : unitInterval := ⟨1/(K : ℝ),by constructor; positivity; exact (div_le_one hK0).mpr hK1⟩
  have hMr : (K : ℝ)^24 ≤ s.card := by exact_mod_cast hM
  have hM0 : 0 < s.card := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : (0 : ℝ) < (K : ℝ)^24) hMr)
  have hpow : (K : ℝ) ≤ (K : ℝ)^20 := by
    exact le_self_pow₀ hK1 (by norm_num)
  have hscale : (K : ℝ)^24*(p : ℝ)^4 = (K : ℝ)^20 := by
    dsimp [p]
    field_simp
  have hprob : (1+2*((K^32 : ℕ) : ℝ))*Real.exp (-(s.card : ℝ)*(p : ℝ)^4/8) < 1 := by
    have hb := mul_le_mul_of_nonneg_right hMr (by positivity : 0 ≤ (p : ℝ)^4)
    have hexp : Real.exp (-(s.card : ℝ)*(p : ℝ)^4/8) ≤ Real.exp (-(K : ℝ)/8) := by
      apply Real.exp_le_exp.mpr
      rw [hscale] at hb
      linarith
    have hle := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 1+2*(K : ℝ)^32)
    push_cast
    exact lt_of_le_of_lt hle hsmall
  obtain ⟨S,hSs,hcard,hfib⟩ := exists_thinning p s (K^32) hM0 hprob
  have hcard' : (s.card : ℝ)/(2*(K : ℝ)) < S.card := by
    simpa [p,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hcard
  have hMpos : (0 : ℝ) < S.card := (by positivity : 0 ≤ (s.card : ℝ)/(2*(K : ℝ))).trans_lt hcard'
  have hcardlo : (K : ℝ)^23/2 < S.card := by
    have he : (K : ℝ)^23/2 = (K : ℝ)^24/(2*(K : ℝ)) := by field_simp
    rw [he]
    exact (div_le_div_of_nonneg_right hMr (by positivity)).trans_lt hcard'
  refine ⟨N,S,hNlo,hNhi,hcardlo,fun q hq => hprime q (hSs hq),?_⟩
  intro h hh
  have hf := hfib h hh
  have hc : (s.card : ℝ) < 2*(K : ℝ)*(S.card : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ (by positivity : 0 < 2*(K : ℝ))).mp hcard'
  have hp0 : 0 < (p : ℝ)^2 := by dsimp [p]; positivity
  have hlt := mul_lt_mul_of_pos_right hc hp0
  have he : 4*(2*(K : ℝ)*(S.card : ℝ))*(p : ℝ)^2 = 8*(S.card : ℝ)/(K : ℝ) := by
    dsimp [p]
    field_simp
    ring
  rw [← he]
  linarith

private theorem short_packet_kernel {N H p q β : ℝ}
    (hN : 0 < N) (hH : 1 ≤ H) (hHN : 2*H^2 ≤ N)
    (hp : p ∈ Icc N (N+H)) (hq : q ∈ Icc N (N+H)) :
    Real.exp (-(p-β*q)^2/16) ≤ Real.exp 1 *
      Real.exp (-((p-q-(⌊(β-1)*N⌋ : ℤ))^2/256)) := by
  let c := (β-1)*N
  let d := p-q-c
  let e := p-β*q
  have hH0 : 0 ≤ H := by linarith
  have hHN' : 2*H ≤ N := by nlinarith only [hH,hHN]
  have hpq : |p-q| ≤ H := abs_le.mpr ⟨by linarith [hp.1,hq.2],by linarith [hp.2,hq.1]⟩
  have hqc : |q-N| ≤ H := by rw [abs_of_nonneg (sub_nonneg.mpr hq.1)]; linarith [hq.2]
  have hc : |c| ≤ |d|+H := by
    have he : c = (p-q)-d := by dsimp [d]; ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  have hid : N*d = N*e+c*(q-N) := by dsimp [c,d,e]; ring
  have hd : N*|d| ≤ N*|e|+|c| * H := by
    have hh := abs_add_le (N*e) (c*(q-N))
    rw [← hid,abs_mul,abs_of_pos hN] at hh
    simp only [abs_mul,abs_of_pos hN] at hh
    exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_left hqc (abs_nonneg c)) _)
  have hh := mul_le_mul_of_nonneg_right hc hH0
  have hh' := mul_le_mul_of_nonneg_right hHN' (abs_nonneg d)
  have hnd : N*|d| ≤ N*(2*|e|+1) := by nlinarith only [hd,hh,hh',hHN]
  have hdb : |d| ≤ 2*|e|+1 := le_of_mul_le_mul_left hnd hN
  have hf : |c-(⌊c⌋ : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le c))]
    linarith only [Int.lt_floor_add_one c]
  have hv : |p-q-(⌊c⌋ : ℝ)| ≤ 2*|e|+2 := by
    calc
      _ = |d+(c-(⌊c⌋ : ℝ))| := congrArg abs (by dsimp only [d]; ring)
      _ ≤ |d|+|c-(⌊c⌋ : ℝ)| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hv2 := pow_le_pow_left₀ (abs_nonneg _) hv 2
  rw [sq_abs] at hv2
  have hv' : (p-q-(⌊c⌋ : ℝ))^2 ≤ 8*e^2+8 := by
    nlinarith only [hv2,sq_nonneg (|e|-1),sq_abs e]
  change Real.exp (-e^2/16) ≤ Real.exp 1*Real.exp (-((p-q-(⌊c⌋ : ℝ))^2/256))
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hv',sq_nonneg e]

private theorem packet_log_kernel {N H p q β : ℝ}
    (hN : 0 < N) (hH : 1 ≤ H) (hHN : 2*H^2 ≤ N)
    (hβ : 0 < β) (hβ2 : β ≤ 2)
    (hp : p ∈ Icc N (N+H)) (hq : q ∈ Icc N (N+H)) :
    Real.exp (-Real.pi*(N*(Real.log p-Real.log q-Real.log β))^2) ≤
      Real.exp 1 * Real.exp (-((p-q-(⌊(β-1)*N⌋ : ℤ))^2/256)) := by
  apply le_trans _ (short_packet_kernel hN hH hHN hp hq)
  have hHN' : H ≤ N := by nlinarith only [hH,hHN]
  have hp0 := hN.trans_le hp.1
  have hq0 := hN.trans_le hq.1
  have hm0 : 0 < max p (β*q) := hp0.trans_le (le_max_left _ _)
  have hmax : max p (β*q) ≤ 4*N := by
    apply max_le
    · linarith only [hp.2,hHN',hN]
    · nlinarith only [mul_le_mul_of_nonneg_right hβ2 hq0.le,hq.2,hHN']
  have hg := (div_le_iff₀ hm0).mp (HTGeometry.abs_sub_div_max_le_abs_log_sub_log hp0 (mul_pos hβ hq0))
  have hg' := hg.trans (mul_le_mul_of_nonneg_left hmax (abs_nonneg _))
  have heq : Real.log p-Real.log (β*q) = Real.log p-Real.log q-Real.log β := by
    rw [Real.log_mul hβ.ne' hq0.ne']; ring
  rw [heq] at hg'
  have hgap : |p-β*q| ≤ 4*|N*(Real.log p-Real.log q-Real.log β)| := by
    rw [abs_mul,abs_of_pos hN]
    nlinarith only [hg']
  have hs := pow_le_pow_left₀ (abs_nonneg _) hgap 2
  simp only [mul_pow,sq_abs] at hs
  have hpi := mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
    (sq_nonneg (N*(Real.log p-Real.log q-Real.log β)))
  apply Real.exp_le_exp.mpr
  nlinarith only [hs,hpi]

private theorem gaussian_nat_data {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c*(n : ℝ)^2)) ∧
    (∑' n : ℕ, Real.exp (-c*(n : ℝ)^2)) ≤ 1 + Real.sqrt (Real.pi/c)/2 ∧
    (∑' n : ℕ, Real.exp (-c*((n : ℝ)+1)^2)) ≤ Real.sqrt (Real.pi/c)/2 := by
  have ha : AntitoneOn (fun x : ℝ => Real.exp (-c*x^2)) (Set.Ici 0) := by
    intro x hx y hy hxy
    apply Real.exp_le_exp.mpr
    have hsquare : x^2 ≤ y^2 := (sq_le_sq₀ hx hy).mpr hxy
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left hsquare hc.le)
  have hi := (integrable_exp_neg_mul_sq hc).integrableOn (s := Set.Ioi 0)
  have hn : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ Real.exp (-c*x^2) := fun _ _ => (Real.exp_pos _).le
  refine ⟨ha.summable_of_integrableOn_Ioi_zero hi hn, ?_, ?_⟩
  · have hb := ha.tsum_le_integral hi hn
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, Real.exp_zero,
      integral_gaussian_Ioi] using hb
  · have hb := ha.tsum_add_one_le_integral hi hn
    simpa only [Nat.cast_add, Nat.cast_one, integral_gaussian_Ioi] using hb

private theorem gaussian_integer_sum {c : ℝ} (hc : 0 < c) (s : Finset ℤ) :
    ∑ v ∈ s, Real.exp (-c * (v : ℝ)^2) ≤ 1 + Real.sqrt (Real.pi / c) := by
  obtain ⟨hs, hb0, hb1⟩ := gaussian_nat_data hc
  have hs1 : Summable (fun n : ℕ => Real.exp (-c*((n : ℝ)+1)^2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  have hneg (n : ℕ) : Real.exp (-c * ((-(n+1) : ℤ) : ℝ)^2) =
      Real.exp (-c*((n : ℝ)+1)^2) := by
    congr 1
    push_cast
    ring
  have hsneg : Summable (fun n : ℕ => Real.exp (-c * ((-(n+1) : ℤ) : ℝ)^2)) := by
    simpa only [hneg] using hs1
  have hsnat : Summable (fun n : ℕ => Real.exp (-c * ((n : ℤ) : ℝ)^2)) := by
    simpa only [Int.cast_natCast] using hs
  have hsi : Summable (fun v : ℤ => Real.exp (-c * (v : ℝ)^2)) :=
    Summable.of_nat_of_neg_add_one (f := fun v : ℤ => Real.exp (-c*(v : ℝ)^2)) hsnat hsneg
  have hsum := hsi.sum_le_tsum s (fun _ _ => (Real.exp_pos _).le)
  have ht := tsum_of_nat_of_neg_add_one (f := fun v : ℤ => Real.exp (-c*(v : ℝ)^2)) hsnat hsneg
  simp only [hneg, Int.cast_natCast] at ht
  rw [ht] at hsum
  linarith only [hsum, hb0, hb1]

private theorem gaussian_integer_scaled {B : ℝ} (hB : 1 ≤ B) (s : Finset ℤ) :
    ∑ v ∈ s, Real.exp (-((v : ℝ)^2 / (16*B^2))) ≤ (1+4*Real.sqrt Real.pi)*B := by
  have hB0 : 0 < B := by linarith
  have hc : 0 < 1/(16*B^2) := by positivity
  have hh := gaussian_integer_sum hc s
  have hsqrt : Real.sqrt (Real.pi / (1/(16*B^2))) = 4*Real.sqrt Real.pi*B := by
    rw [div_div_eq_mul_div, div_one, show Real.pi*(16*B^2) = Real.pi*(4*B)^2 by ring,
      Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq (by positivity)]
    ring
  rw [hsqrt] at hh
  have heq : (fun v : ℤ => Real.exp (-(1/(16*B^2))*(v : ℝ)^2)) =
      (fun v : ℤ => Real.exp (-((v : ℝ)^2/(16*B^2)))) := by
    ext v
    congr 1
    ring
  rw [heq] at hh
  nlinarith only [hh, hB]

private theorem gaussian_fibre_sum {s : Finset (ℕ × ℕ)} (f : ℕ × ℕ → ℤ)
    {D B : ℝ} (hD : 0 ≤ D) (hB : 1 ≤ B)
    (hf : ∀ v ∈ s.image f, ((s.filter (fun x => f x = v)).card : ℝ) ≤ D) :
    ∑ x ∈ s, Real.exp (-((f x : ℝ)^2/(16*B^2))) ≤ D*(1+4*Real.sqrt Real.pi)*B := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image f) (g := f) (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    (fun x => Real.exp (-((f x : ℝ)^2/(16*B^2))))]
  calc
    _ ≤ ∑ v ∈ s.image f, D*Real.exp (-((v : ℝ)^2/(16*B^2))) := by
      apply Finset.sum_le_sum
      intro v hv
      have heq : (∑ x ∈ s.filter (fun x => f x=v), Real.exp (-((f x : ℝ)^2/(16*B^2)))) =
          ((s.filter (fun x => f x=v)).card : ℝ)*Real.exp (-((v : ℝ)^2/(16*B^2))) := by
        calc
          _ = ∑ _x ∈ s.filter (fun x => f x=v), Real.exp (-((v : ℝ)^2/(16*B^2))) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [(Finset.mem_filter.mp hx).2]
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      rw [heq]
      exact mul_le_mul_of_nonneg_right (hf v hv) (Real.exp_pos _).le
    _ = D * ∑ v ∈ s.image f, Real.exp (-((v : ℝ)^2/(16*B^2))) := (Finset.mul_sum _ _ _).symm
    _ ≤ D * ((1+4*Real.sqrt Real.pi)*B) := mul_le_mul_of_nonneg_left (gaussian_integer_scaled hB _) hD
    _ = _ := by ring


private def offPairs (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ S).filter (fun x => x.1 ≠ x.2)

private theorem difference_fibre_bound {N H : ℕ} {S : Finset ℕ} {D : ℝ}
    (hS : ∀ p ∈ S, N ≤ p ∧ p ≤ N+H)
    (hD : ∀ h ∈ Finset.Icc 1 H,
      ((S.filter (fun a => a+h ∈ S)).card : ℝ) ≤ D)
    (z : ℤ) (v : ℤ)
    (hv : v ∈ (offPairs S).image (fun x => (x.1 : ℤ)-x.2-z)) :
    (((offPairs S).filter (fun x => (x.1 : ℤ)-x.2-z=v)).card : ℝ) ≤ D := by
  obtain ⟨x,hx,hxv⟩ := Finset.mem_image.mp hv
  have hx' := Finset.mem_filter.mp hx
  have hxS := Finset.mem_product.mp hx'.1
  have hxp := hS x.1 hxS.1
  have hxq := hS x.2 hxS.2
  let F := (offPairs S).filter (fun y => (y.1 : ℤ)-y.2-z=v)
  have hF (y : ℕ × ℕ) (hy : y ∈ F) :
      y.1 ∈ S ∧ y.2 ∈ S ∧ (y.1 : ℤ)-y.2 = (x.1 : ℤ)-x.2 := by
    have hy' := Finset.mem_filter.mp hy
    have hys := Finset.mem_product.mp (Finset.mem_filter.mp hy'.1).1
    exact ⟨hys.1,hys.2,by omega⟩
  rcases lt_or_gt_of_ne hx'.2 with hlt | hgt
  · let h := x.2-x.1
    have hh : h ∈ Finset.Icc 1 H := by apply Finset.mem_Icc.mpr; dsimp [h]; omega
    have hm : Set.MapsTo (fun y : ℕ × ℕ => y.1) F (S.filter (fun a => a+h ∈ S)) := by
      intro y hy
      have hy' := hF y hy
      have he : y.1+h=y.2 := by dsimp [h]; omega
      exact Finset.mem_filter.mpr ⟨hy'.1,he ▸ hy'.2.1⟩
    have hi : (F : Set (ℕ × ℕ)).InjOn (fun y => y.1) := by
      intro y hy w hw he
      have hy' := hF y hy
      have hw' := hF w hw
      change y.1 = w.1 at he
      apply Prod.ext he
      omega
    have hcard : (F.card : ℝ) ≤ (S.filter (fun a => a+h ∈ S)).card := by
      exact_mod_cast Finset.card_le_card_of_injOn (fun y : ℕ × ℕ => y.1) hm hi
    exact hcard.trans (hD h hh)
  · let h := x.1-x.2
    have hh : h ∈ Finset.Icc 1 H := by apply Finset.mem_Icc.mpr; dsimp [h]; omega
    have hm : Set.MapsTo (fun y : ℕ × ℕ => y.2) F (S.filter (fun a => a+h ∈ S)) := by
      intro y hy
      have hy' := hF y hy
      have he : y.2+h=y.1 := by dsimp [h]; omega
      exact Finset.mem_filter.mpr ⟨hy'.2.1,he ▸ hy'.1⟩
    have hi : (F : Set (ℕ × ℕ)).InjOn (fun y => y.2) := by
      intro y hy w hw he
      have hy' := hF y hy
      have hw' := hF w hw
      change y.2 = w.2 at he
      apply Prod.ext _ he
      omega
    have hcard : (F.card : ℝ) ≤ (S.filter (fun a => a+h ∈ S)).card := by
      exact_mod_cast Finset.card_le_card_of_injOn (fun y : ℕ × ℕ => y.2) hm hi
    exact hcard.trans (hD h hh)

private def freq (β : ℝ) (p q : ℕ) : ℝ := Real.log p-Real.log q-Real.log β

/-- Exact connected Gaussian spectral sum of a unit-energy packet. -/
def connectedPacketSpectral (S : Finset ℕ) (N β t : ℝ) : ℂ :=
  ((S.card : ℂ)⁻¹)*∑ x ∈ offPairs S,
    Complex.exp (((freq β x.1 x.2*t : ℝ) : ℂ)*Complex.I)*
      (Real.exp (-Real.pi*(N*freq β x.1 x.2)^2) : ℂ)

private theorem packet_spectral_bound {N H : ℕ} {S : Finset ℕ} {D β : ℝ}
    (hN : 0 < N) (hH : 1 ≤ H) (hHN : 2*H^2 ≤ N) (hD0 : 0 ≤ D)
    (hS : ∀ p ∈ S, N ≤ p ∧ p ≤ N+H)
    (hD : ∀ h ∈ Finset.Icc 1 H,
      ((S.filter (fun a => a+h ∈ S)).card : ℝ) ≤ D)
    (hβ : 1/2 ≤ β) (hβ2 : β ≤ 2) (t : ℝ) :
    ‖connectedPacketSpectral S N β t‖ ≤
      ((S.card : ℝ)⁻¹)*(Real.exp 1*D*(1+4*Real.sqrt Real.pi)*4) := by
  let z : ℤ := ⌊(β-1)*N⌋
  let f : ℕ × ℕ → ℤ := fun x => (x.1 : ℤ)-x.2-z
  have hf := gaussian_fibre_sum (s := offPairs S) f hD0 (by norm_num : (1 : ℝ) ≤ 4)
    (difference_fibre_bound hS hD z)
  have hkernel (x : ℕ × ℕ) (hx : x ∈ offPairs S) :
      Real.exp (-Real.pi*((N : ℝ)*freq β x.1 x.2)^2) ≤
        Real.exp 1*Real.exp (-((f x : ℝ)^2/(16*(4 : ℝ)^2))) := by
    have hx' := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
    have hp := hS x.1 hx'.1
    have hq := hS x.2 hx'.2
    have ht := packet_log_kernel (by exact_mod_cast hN) (by exact_mod_cast hH)
      (by exact_mod_cast hHN) (by linarith : 0 < β) hβ2
      (show (x.1 : ℝ) ∈ Icc (N : ℝ) (N+H) from
        ⟨by exact_mod_cast hp.1,by exact_mod_cast hp.2⟩)
      (show (x.2 : ℝ) ∈ Icc (N : ℝ) (N+H) from
        ⟨by exact_mod_cast hq.1,by exact_mod_cast hq.2⟩)
    simpa only [f,z,freq,Int.cast_sub,Int.cast_natCast,show (16 : ℝ)*4^2=256 by norm_num] using ht
  have hsum := Finset.sum_le_sum hkernel
  rw [← Finset.mul_sum] at hsum
  have htotal : (∑ x ∈ offPairs S, Real.exp (-Real.pi*((N : ℝ)*freq β x.1 x.2)^2)) ≤
      Real.exp 1*D*(1+4*Real.sqrt Real.pi)*4 := by
    exact hsum.trans ((mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le).trans_eq (by ring))
  have hnorm (x : ℕ × ℕ) :
      ‖Complex.exp (((freq β x.1 x.2*t : ℝ) : ℂ)*Complex.I)*
        (Real.exp (-Real.pi*((N : ℝ)*freq β x.1 x.2)^2) : ℂ)‖ =
        Real.exp (-Real.pi*((N : ℝ)*freq β x.1 x.2)^2) := by
    rw [norm_mul,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,Complex.ofReal_im,
      Complex.I_im,zero_mul,sub_self,Real.exp_zero,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  unfold connectedPacketSpectral
  rw [norm_mul,norm_inv,Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  simpa only [hnorm] using htotal

private theorem normalized_cubic_integral (N : ℝ) (S : Finset ℕ) :
    (∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
      (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
        zetaChi (linePt t)*normalizedPrimePacketCubicOffDiagonal S t).re =
      (Real.sqrt (S.card:ℝ))⁻¹ ^ 3 *
        (∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
          (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
            zetaChi (linePt t)*coherentPrimePacketCubicOffDiagonal S t).re := by
  have he (t:ℝ) : (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
      zetaChi (linePt t)*normalizedPrimePacketCubicOffDiagonal S t =
      (((Real.sqrt (S.card:ℝ))⁻¹ ^ 3 : ℝ):ℂ)*
        ((bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
          zetaChi (linePt t)*coherentPrimePacketCubicOffDiagonal S t) := by
    unfold normalizedPrimePacketCubicOffDiagonal
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,Complex.re_ofReal_mul]

private theorem thin_packet_cubic_data : ∃ N₀ : ℝ, 0 < N₀ ∧
    ∀ (K N : ℕ) (S : Finset ℕ), 2 ≤ K → N₀ ≤ N →
      64*K^64 ≤ N → N ≤ 128*K^64 → (K : ℝ)^23/2 < S.card →
      (∀ p ∈ S, N ≤ p ∧ p ≤ N+K^32) →
      (∑ _p ∈ S, ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖^2) = 1 ∧
      ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖ ≤ 1/(K : ℝ) ∧
      physicalCubicPacketScale N*((K : ℝ)^2/1024) ≤
        (∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
          (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
            zetaChi (linePt t)*normalizedPrimePacketCubicOffDiagonal S t).re := by
  obtain ⟨N₀,hN₀,hb⟩ := exists_coherentPrimePacketCubicOffDiagonal_positive
  refine ⟨N₀,hN₀,?_⟩
  intro K N S hK hNlarge hNlo hNhi hcard hS
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  have hK1 : (1 : ℝ) ≤ K := by linarith
  have hNloR : (64 : ℝ)*(K : ℝ)^64 ≤ N := by exact_mod_cast hNlo
  have hNhiR : (N : ℝ) ≤ 128*(K : ℝ)^64 := by exact_mod_cast hNhi
  have hNpos := hN₀.trans_le hNlarge
  have hH1 : (1 : ℝ) ≤ (K : ℝ)^32 := one_le_pow₀ hK1
  have hHsq : ((K : ℝ)^32)^2 = (K : ℝ)^64 := by ring
  have hplateau : (K : ℝ)^32 ≤ (N : ℝ)/32 := by nlinarith only [hNloR,hHsq,hH1]
  have hcohere : 2*Real.pi*((K : ℝ)^32)^2/(N : ℝ) ≤ 1/4 := by
    apply (div_le_iff₀ hNpos).mpr
    have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (sq_nonneg ((K : ℝ)^32))
    nlinarith only [hNloR,hHsq,hpi]
  have hSreal : ∀ p ∈ S, (p : ℝ) ∈ Icc (N : ℝ) (N+(K : ℝ)^32) := by
    intro p hp
    exact ⟨by exact_mod_cast (hS p hp).1,by exact_mod_cast (hS p hp).2⟩
  have h3 : (K : ℝ)^3 ≤ (K : ℝ)^23 := pow_le_pow_right₀ hK1 (by norm_num)
  have hMflat : (K : ℝ)^2 ≤ S.card := by
    have hh := mul_le_mul_of_nonneg_right hKr (sq_nonneg (K : ℝ))
    nlinarith only [h3,hcard,hh]
  have hM : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hMflat
  have hM2 : 2 ≤ S.card := by
    have hh : (2 : ℝ) ≤ S.card := by nlinarith only [hMflat,hKr]
    exact_mod_cast hh
  have hl := hb N ((K : ℝ)^32) hNlarge (by positivity) hplateau hcohere S hM2 hSreal
  have hs : 0 < Real.sqrt (S.card : ℝ) := Real.sqrt_pos.mpr hM
  have hs2 := Real.sq_sqrt hM.le
  have hn : ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖ = (Real.sqrt (S.card : ℝ))⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  have henergy : (∑ _p ∈ S, ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖^2) = 1 := by
    simp only [hn,Finset.sum_const,nsmul_eq_mul,inv_pow,hs2]
    exact mul_inv_cancel₀ hM.ne'
  have hflat : ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖ ≤ 1/(K : ℝ) := by
    rw [hn,← one_div]
    exact one_div_le_one_div_of_le hK0 (Real.le_sqrt_of_sq_le hMflat)
  have hnormmass : (Real.pi*Real.sqrt N/16)*(S.card : ℝ)*Real.sqrt (S.card : ℝ) ≤
      (∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
        (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
          zetaChi (linePt t)*normalizedPrimePacketCubicOffDiagonal S t).re := by
    rw [normalized_cubic_integral]
    have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (Real.sqrt (S.card : ℝ))⁻¹^3)
    have he : (Real.pi*Real.sqrt N/16)*(S.card : ℝ)*Real.sqrt (S.card : ℝ) =
        (Real.sqrt (S.card : ℝ))⁻¹^3*((Real.pi*Real.sqrt N/16)*(S.card : ℝ)^3) := by
      rw [← hs2]
      simp only [Real.sqrt_sq (Real.sqrt_nonneg _)]
      field_simp
    rw [he]
    exact hh
  have hsqrtN : Real.sqrt N ≤ 12*(K : ℝ)^32 := by
    nlinarith only [hNhiR,hHsq,Real.sq_sqrt hNpos.le,Real.sqrt_nonneg (N : ℝ),hH1]
  have hsqrtM : (K : ℝ)^11/2 ≤ Real.sqrt (S.card : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    have hh : (K : ℝ)^22 ≤ (K : ℝ)^23 := pow_le_pow_right₀ hK1 (by norm_num)
    have he : ((K : ℝ)^11/2)^2 = (K : ℝ)^22/4 := by ring
    rw [he]
    nlinarith only [hh,hcard,pow_nonneg hK0.le 22]
  have hcore : Real.sqrt N*(K : ℝ)^2 ≤ 48*(S.card : ℝ)*Real.sqrt (S.card : ℝ) := by
    have hh := mul_le_mul hcard.le hsqrtM (by positivity) hM.le
    have he : ((K : ℝ)^23/2)*((K : ℝ)^11/2) = (K : ℝ)^34/4 := by ring
    rw [he] at hh
    have hN' := mul_le_mul_of_nonneg_right hsqrtN (sq_nonneg (K : ℝ))
    have he' : 12*(K : ℝ)^32*(K : ℝ)^2 = 12*(K : ℝ)^34 := by ring
    rw [he'] at hN'
    nlinarith only [hh,hN']
  have hscale : physicalCubicPacketScale N*((K : ℝ)^2/1024) ≤
      (Real.pi*Real.sqrt N/16)*(S.card : ℝ)*Real.sqrt (S.card : ℝ) := by
    calc
      _ = (Real.pi*Real.sqrt N/768)*(Real.sqrt N*(K : ℝ)^2) := by
        unfold physicalCubicPacketScale
        ring_nf
        rw [Real.sq_sqrt hNpos.le]
        ring
      _ ≤ (Real.pi*Real.sqrt N/768)*(48*(S.card : ℝ)*Real.sqrt (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = _ := by ring
  exact ⟨henergy,hflat,hscale.trans hnormmass⟩


/-- Critical-height Gaussian average of the actual unit-energy prime packet. -/
def packetAverage (S : Finset ℕ) (N β t : ℝ) : ℂ :=
  ∫ u : ℝ, (Real.exp (-Real.pi*u^2) : ℂ) *
    Complex.exp ((((-Real.log β)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
    normalizedCoherentPrimePacketPoly S (t+2*Real.pi*N*u) *
    (starRingEnd ℂ) (normalizedCoherentPrimePacketPoly S (t+2*Real.pi*N*u))

/-- Complete diagonal packet, including twists arbitrarily close to one. -/
def packetDiagonal (N β t : ℝ) : ℂ :=
  Complex.exp (((-Real.log β*t : ℝ) : ℂ)*Complex.I)*
    (Real.exp (-Real.pi*(N*Real.log β)^2) : ℂ)

private theorem pair_phase (N β t u : ℝ) (p q : ℕ) :
    (Real.exp (-Real.pi*u^2) : ℂ) *
      Complex.exp ((((-Real.log β)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
      bourgainOscillation ((t+2*Real.pi*N*u)*Real.log p) *
      (starRingEnd ℂ) (bourgainOscillation ((t+2*Real.pi*N*u)*Real.log q)) =
      Complex.exp (((freq β p q*t : ℝ) : ℂ)*Complex.I) *
        bourgainGaussianFourierIntegrand (N*freq β p q) u := by
  have hpj : (starRingEnd ℂ) (Complex.exp ((((t+2*Real.pi*N*u)*Real.log q : ℝ) : ℂ)*Complex.I)) =
      Complex.exp (-((((t+2*Real.pi*N*u)*Real.log q : ℝ) : ℂ)*Complex.I)) := by
    rw [← Complex.exp_conj]
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg]
  have hg : (Real.exp (-Real.pi*u^2) : ℂ) = Complex.exp (-((Real.pi : ℂ)*(u : ℂ)^2)) := by
    rw [Complex.ofReal_exp]
    push_cast
    congr 1
    ring
  unfold bourgainOscillation
  simp only [mul_comm Complex.I]
  rw [hpj,hg]
  unfold bourgainGaussianFourierIntegrand
  simp_rw [← Complex.exp_add]
  congr 1
  unfold freq
  push_cast
  ring

private theorem raw_average (S : Finset ℕ) (N β t : ℝ) :
    (∫ u : ℝ, (Real.exp (-Real.pi*u^2) : ℂ) *
      Complex.exp ((((-Real.log β)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
      coherentPrimePacketPoly S (t+2*Real.pi*N*u) *
      (starRingEnd ℂ) (coherentPrimePacketPoly S (t+2*Real.pi*N*u))) =
    ∑ p ∈ S, ∑ q ∈ S, Complex.exp (((freq β p q*t : ℝ) : ℂ)*Complex.I)*
      (Real.exp (-Real.pi*(N*freq β p q)^2) : ℂ) := by
  have hpoint (u : ℝ) :
      (Real.exp (-Real.pi*u^2) : ℂ) *
        Complex.exp ((((-Real.log β)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
        coherentPrimePacketPoly S (t+2*Real.pi*N*u) *
        (starRingEnd ℂ) (coherentPrimePacketPoly S (t+2*Real.pi*N*u)) =
      ∑ p ∈ S, ∑ q ∈ S, Complex.exp (((freq β p q*t : ℝ) : ℂ)*Complex.I)*
        bourgainGaussianFourierIntegrand (N*freq β p q) u := by
    simp only [coherentPrimePacketPoly,map_sum,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    exact pair_phase N β t u p q
  have hi (p q : ℕ) : Integrable (fun u : ℝ =>
      Complex.exp (((freq β p q*t : ℝ) : ℂ)*Complex.I)*
        bourgainGaussianFourierIntegrand (N*freq β p q) u) :=
    (integrable_bourgainGaussianFourierIntegrand _).const_mul _
  simp_rw [hpoint]
  rw [MeasureTheory.integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hi p q))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [MeasureTheory.integral_finsetSum _ (fun q _ => hi p q)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [MeasureTheory.integral_const_mul,integral_bourgainGaussianFourierIntegrand]

private theorem average_normalization (S : Finset ℕ) (N β t : ℝ) :
    packetAverage S N β t = (S.card : ℂ)⁻¹ *
      ∑ p ∈ S, ∑ q ∈ S, Complex.exp (((freq β p q*t : ℝ) : ℂ)*Complex.I)*
        (Real.exp (-Real.pi*(N*freq β p q)^2) : ℂ) := by
  have hs : (Real.sqrt (S.card : ℝ) : ℂ)*(Real.sqrt (S.card : ℝ) : ℂ) = (S.card : ℂ) := by
    rw [← Complex.ofReal_mul,← pow_two,Real.sq_sqrt (Nat.cast_nonneg _)]
    rfl
  have hc : (Real.sqrt (S.card : ℝ) : ℂ)⁻¹ *
      (starRingEnd ℂ) (Real.sqrt (S.card : ℝ) : ℂ)⁻¹ = (S.card : ℂ)⁻¹ := by
    rw [map_inv₀,Complex.conj_ofReal,← mul_inv,hs]
  have he (u : ℝ) :
      (Real.exp (-Real.pi*u^2) : ℂ) *
        Complex.exp ((((-Real.log β)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
        normalizedCoherentPrimePacketPoly S (t+2*Real.pi*N*u) *
        (starRingEnd ℂ) (normalizedCoherentPrimePacketPoly S (t+2*Real.pi*N*u)) =
      (S.card : ℂ)⁻¹ * ((Real.exp (-Real.pi*u^2) : ℂ) *
        Complex.exp ((((-Real.log β)*(t+2*Real.pi*N*u) : ℝ) : ℂ)*Complex.I) *
        coherentPrimePacketPoly S (t+2*Real.pi*N*u) *
        (starRingEnd ℂ) (coherentPrimePacketPoly S (t+2*Real.pi*N*u))) := by
    unfold normalizedCoherentPrimePacketPoly
    rw [map_mul]
    rw [← hc]
    ring
  unfold packetAverage
  simp_rw [he]
  rw [MeasureTheory.integral_const_mul,raw_average]

/-- No boundary or near-one twist is discarded in the connected decomposition. -/
theorem packetAverage_sub_diagonal {S : Finset ℕ} (hS : 0 < S.card) (N β t : ℝ) :
    packetAverage S N β t-packetDiagonal N β t = connectedPacketSpectral S N β t := by
  classical
  rw [average_normalization]
  let F : ℕ → ℕ → ℂ := fun p q => Complex.exp (((freq β p q*t : ℝ) : ℂ)*Complex.I)*
    (Real.exp (-Real.pi*(N*freq β p q)^2) : ℂ)
  have hd (p : ℕ) : F p p = packetDiagonal N β t := by
    simp only [F,freq,sub_self,zero_sub,mul_neg,neg_sq,packetDiagonal]
  have he (p q : ℕ) : F p q = (if p ≠ q then F p q else 0)+(if p=q then F p q else 0) := by
    by_cases h : p=q <;> simp [h]
  have hsplit : (∑ p ∈ S, ∑ q ∈ S, F p q) =
      (∑ x ∈ offPairs S, F x.1 x.2)+(S.card : ℂ)*packetDiagonal N β t := by
    conv_lhs => arg 2; ext p; arg 2; ext q; rw [he p q]
    simp only [Finset.sum_add_distrib]
    congr 1
    · unfold offPairs
      rw [Finset.sum_filter,Finset.sum_product]
    · have hh (p : ℕ) (hp : p ∈ S) : (∑ q ∈ S, if p=q then F p q else 0) = packetDiagonal N β t := by
        simp [hp,hd]
      simp only [Finset.sum_congr rfl hh,Finset.sum_const,nsmul_eq_mul]
  change (S.card : ℂ)⁻¹*(∑ p ∈ S, ∑ q ∈ S, F p q)-packetDiagonal N β t = _
  rw [hsplit,mul_add]
  have hM : (S.card : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hS)
  rw [← mul_assoc,inv_mul_cancel₀ hM,one_mul,add_sub_cancel_right]
  rfl

/-- Actual prime packets simultaneously have unit energy, vanishing coefficient
size, uniform all-real connected Gaussian mixing, and a signed noncontracting
physical cubic that diverges per unit height. No selection or moment premise
is assumed. This concerns coherent subpackets, not the full Gaussian band. -/
theorem exists_prime_packets_connected_mixing_cubic_divergence :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ K : ℕ in atTop, ∃ (N : ℕ) (S : Finset ℕ),
      64*K^64 ≤ N ∧ N ≤ 128*K^64 ∧ (K : ℝ)^23/2 < S.card ∧
      (∀ p ∈ S, p.Prime ∧ N ≤ p ∧ p ≤ N+K^32) ∧
      (∑ _p ∈ S, ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖^2) = 1 ∧
      ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖ ≤ 1/(K : ℝ) ∧
      (∀ β : ℝ, 1/2 ≤ β → β ≤ 2 → ∀ t : ℝ,
        ‖packetAverage S N β t-packetDiagonal N β t‖ ≤ C/(K : ℝ)) ∧
      physicalCubicPacketScale N*((K : ℝ)^2/1024) ≤
        (∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
          (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
            zetaChi (linePt t)*normalizedPrimePacketCubicOffDiagonal S t).re := by
  let C := 32*Real.exp 1*(1+4*Real.sqrt Real.pi)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  obtain ⟨N₀,hN₀,hcubic⟩ := thin_packet_cubic_data
  have ht : Tendsto (fun K : ℕ => 64*(K : ℝ)^64) atTop atTop :=
    (tendsto_const_mul_pow_atTop (by norm_num : (64 : ℕ) ≠ 0)
      (by norm_num : (0 : ℝ) < 64)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_exists_thin_prime_packet,ht.eventually_ge_atTop N₀,
    eventually_ge_atTop (2 : ℕ)] with K hthin hlarge hK
  obtain ⟨N,S,hNlo,hNhi,hcard,hprime,hfib⟩ := hthin
  have hS : ∀ p ∈ S, N ≤ p ∧ p ≤ N+K^32 := fun p hp => (hprime p hp).2
  have hNloR : (64 : ℝ)*(K : ℝ)^64 ≤ N := by exact_mod_cast hNlo
  have hc := hcubic K N S hK (hlarge.trans hNloR) hNlo hNhi hcard hS
  refine ⟨N,S,hNlo,hNhi,hcard,hprime,hc.1,hc.2.1,?_,hc.2.2⟩
  intro β hβ hβ2 t
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hM : (0 : ℝ) < S.card := (by positivity : 0 ≤ (K : ℝ)^23/2).trans_lt hcard
  have hN : 0 < N := by exact_mod_cast hN₀.trans_le (hlarge.trans hNloR)
  have hH : 1 ≤ K^32 := one_le_pow₀ (by omega : 1 ≤ K)
  have hHN : 2*(K^32)^2 ≤ N := by
    have he : (K^32)^2 = K^64 := by ring
    rw [he]
    omega
  have hD0 : 0 ≤ 8*(S.card : ℝ)/(K : ℝ) := by positivity
  rw [packetAverage_sub_diagonal (by exact_mod_cast hM)]
  have hh := packet_spectral_bound hN hH hHN hD0 hS (fun h hh => (hfib h hh).le) hβ hβ2 t
  apply hh.trans_eq
  dsimp [C]
  field_simp
  ring

end RHTower.PrimePacketThinning
