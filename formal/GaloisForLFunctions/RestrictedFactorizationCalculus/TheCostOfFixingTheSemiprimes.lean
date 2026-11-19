import GaloisForLFunctions.RestrictedFactorizationCalculus.PrescribingTheSquarefreeFixedVertices
import GaloisForLFunctions.RHTower.SemiprimeWindowCount
import GaloisForLFunctions.RHTower.Sieve.AlmostPrimeGlobalCount

/-!
# The price of fixing the semiprimes

The image of every prime is a distinct classification error if the
requested fixed vertices are the squarefree semiprimes. Arbitrarily
slowly diverging error remains attainable with sublinear unpaid count,
but a short matching incurs essentially one error for every prime.
-/

noncomputable section

open Finset Filter
open GaloisForLFunctions.QuantitativeFactorizationMatching RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The squarefree integers with precisely two prime factors. -/
def squarefreeSemiprimes : Set ℕ := {n | Squarefree n ∧ n.primeFactors.card=2}

private theorem partner_of_prime {p n : ℕ} (hp : p.Prime) (edge : GlobalDyadicOneTwoRel p n) :
    n ∈ squarefreeSemiprimes := by
  obtain ⟨_,_,_,c,a,b,d,ha,hb,hd,lt,h⟩ := edge
  apply RHTower.PrimeCells.squarefree_card_primeFactors_two_iff.mpr
  rcases h with ⟨pa,e⟩ | ⟨_,e⟩
  · have eq : a=p := (Nat.prime_dvd_prime_iff_eq ha hp).mp (pa ▸ dvd_mul_left a c)
    have one : c=1 := Nat.eq_of_mul_eq_mul_right ha.pos
      (show c*a=1*a by rw [←pa,one_mul,eq])
    exact ⟨b,d,hb,hd,lt,by simpa only [one,one_mul] using e⟩
  · have wrong (q : ℕ) (hq : q.Prime) (dv : q ∣ b*d) : q=p :=
      (Nat.prime_dvd_prime_iff_eq hq hp).mp (e ▸ dvd_mul_of_dvd_right dv c)
    exact (lt.ne ((wrong b hb (dvd_mul_right ..)).trans (wrong d hd (dvd_mul_left ..)).symm)).elim

private theorem error_at_image (G : ℕ → ℕ) (back : Function.Involutive G)
    (legal : ∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) {p X : ℕ} (hp : p.Prime)
    (bound : G p ≤ X) : G p ∈ supportErrors G squarefreeSemiprimes X := by
  rcases legal p with eq | edge
  · rw [eq]
    have absent : p ∉ squarefreeSemiprimes := by
      intro h
      have hc := h.2
      rw [hp.primeFactors,card_singleton] at hc
      omega
    have hi := mem_Icc.mpr ⟨hp.pos,eq ▸ bound⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hi,Irreducible.squarefree hp⟩,
      fun h => (h.mp eq).elim hp.ne_one absent⟩
  · have hit := partner_of_prime hp edge
    have different : p ≠ G p := by
      intro eq
      have psemi : p ∈ squarefreeSemiprimes := eq ▸ hit
      have h := psemi.2
      rw [hp.primeFactors,card_singleton] at h
      omega
    have hi := mem_Icc.mpr ⟨Nat.pos_of_ne_zero edge.2.1.ne_zero,bound⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hi,edge.2.1⟩,
      fun h => different ((back p).symm.trans (h.mpr (Or.inr hit)))⟩

/-- Every prime whose image has arrived by X charges a different
squarefree misclassification by X. There is no restriction on the
relative sizes of the prime cutoff and the observation cutoff. -/
theorem images_of_primes_force_distinct_support_errors (G : ℕ → ℕ) (back : Function.Involutive G)
    (legal : ∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) (T X : ℕ) :
    ((Nat.primesLE T).filter (fun p => G p ≤ X)).card ≤ (supportErrors G squarefreeSemiprimes X).card :=
  card_le_card_of_injOn G (fun _ h => error_at_image G back legal
    (Nat.prime_of_mem_primesLE (mem_filter.mp h).1) (mem_filter.mp h).2)
    (fun _ _ _ _ h => back.injective h)

/-- All legal matchings have unboundedly many errors for the semiprime
target. A matching of sublinear displacement pays the entire prime count
through T by every sufficiently late wall above (1+δ)T. -/
theorem unavoidable_errors_for_the_semiprime_support (G : ℕ → ℕ) (back : Function.Involutive G)
    (legal : ∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) :
    Tendsto (fun X => (supportErrors G squarefreeSemiprimes X).card) atTop atTop ∧
    ((∀ δ : ℝ,0<δ → ∀ᶠ n : ℕ in atTop,|(G n:ℝ)-n| ≤ δ*n) →
      ∀ δ : ℝ,0<δ → ∀ᶠ X : ℕ in atTop,∀ T : ℕ,(1+δ)*T ≤ X →
        T.primeCounting ≤ (supportErrors G squarefreeSemiprimes X).card) := by
  constructor
  · apply tendsto_atTop.mpr
    intro K
    obtain ⟨T,large⟩ := (Nat.tendsto_primeCounting.eventually_ge_atTop K).exists
    filter_upwards [eventually_ge_atTop ((Nat.primesLE T).sup G)] with X late
    have each (p : ℕ) (hp : p ∈ Nat.primesLE T) : G p ≤ X := (Finset.le_sup hp).trans late
    have bound := images_of_primes_force_distinct_support_errors G back legal T X
    rw [filter_eq_self.mpr each,Nat.primesLE_card_eq_primeCounting] at bound
    exact large.trans bound
  · intro short δ hδ
    obtain ⟨N,fromN⟩ := eventually_atTop.mp (short δ hδ)
    filter_upwards [eventually_ge_atTop ((range N).sup G)] with X late
    intro T size
    have each (p : ℕ) (hp : p ∈ Nat.primesLE T) : G p ≤ X := by
      by_cases before : p<N
      · exact (Finset.le_sup (f := G) (mem_range.mpr before)).trans late
      · have small := (abs_le.mp (fromN _ (le_of_not_gt before))).2
        have gap := mul_le_mul_of_nonneg_left ((Nat.cast_le (α := ℝ)).mpr (Nat.mem_primesLE.mp hp).1)
          (show 0 ≤ 1+δ by linarith only [hδ])
        exact Nat.cast_le.mp (by linarith only [small,gap,size] : (G p:ℝ) ≤ X)
    have bound := images_of_primes_force_distinct_support_errors G back legal T X
    simpa only [filter_eq_self.mpr each,Nat.primesLE_card_eq_primeCounting] using bound

private theorem semiprimes_have_density_zero (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop,(((Icc 1 X).filter (· ∈ squarefreeSemiprimes)).card:ℝ) ≤ ε*X := by
  obtain ⟨C,hC,bound⟩ := exists_squarefreeOmegaCount_two_bound
  let d := ε/(2*C)
  have pos : 0<d := div_pos hε (by positivity)
  have top : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [top (Real.isLittleO_log_id_atTop.bound pos),top.eventually_ge_atTop 1,
    top.eventually_ge_atTop (|mertensUpperConst|/d),eventually_ge_atTop (2:ℕ)] with X logBound log1 const hx
  let L := Real.log (X:ℝ)
  have Lpos : 0<L := zero_lt_one.trans_le log1
  change ‖Real.log L‖ ≤ d*‖L‖ at logBound
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg log1),abs_of_nonneg Lpos.le] at logBound
  have small := (le_abs_self mertensUpperConst).trans ((div_le_iff₀ pos).mp const)
  have price : C*(logLog X+mertensUpperConst)/L ≤ ε := (div_le_iff₀ Lpos).mpr (by
    change C*(Real.log L+mertensUpperConst) ≤ ε*L
    have eq : C*(2*d)=ε := by dsimp only [d]; field_simp
    rw [←eq]
    linarith only [mul_le_mul_of_nonneg_left (add_le_add logBound small) hC.le])
  change (squarefreeOmegaCount 2 X:ℝ) ≤ _
  have hh := bound X hx
  simp only [pow_one] at hh
  exact hh.trans ((le_of_eq (by dsimp only [L]; ring : C*(X*(logLog X+mertensUpperConst)/Real.log X)=
    C*(logLog X+mertensUpperConst)/L*X)).trans (mul_le_mul_of_nonneg_right price (Nat.cast_nonneg X)))

/-- Arbitrarily slow divergence of the classification error is sufficient
on this particular density-zero set, even though bounded error fails. -/
theorem arbitrarily_slow_error_when_fixing_the_semiprimes (w : ℕ → ℝ)
    (pos : ∀ n,0 ≤ w n) (top : Tendsto w atTop atTop) :
    ∃ G : ℕ → ℕ,Function.Involutive G ∧ (∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X) ∧
      ∀ X : ℕ,((supportErrors G squarefreeSemiprimes X).card:ℝ) ≤ w X ∧
        (supportErrors G squarefreeSemiprimes X).card ≤ Nat.sqrt X :=
  (realizable_sparse_squarefree_supports squarefreeSemiprimes (fun _ h => h.1)).mp
    semiprimes_have_density_zero w pos top

private theorem signed_semiprime_target {X : ℕ} (hX : 0<X) :
    (∑ n ∈ (squarefreeOf (Icc 1 X)).filter (fun n => n=1 ∨ n ∈ squarefreeSemiprimes),(μ n:ℝ))=
      (squarefreeOmegaCount 2 X:ℝ)+1 := by
  let C := (Icc 1 X).filter (· ∈ squarefreeSemiprimes)
  have same : (squarefreeOf (Icc 1 X)).filter (fun n => n=1 ∨ n ∈ squarefreeSemiprimes)=insert 1 C := by
    ext n
    simp only [squarefreeOf,mem_filter,mem_insert,C]
    by_cases eq : n=1
    · subst n; simp [hX]
    · simp only [eq,false_or]
      exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.1⟩,h.2⟩⟩
  have absent : 1 ∉ C := by simp [C,squarefreeSemiprimes]
  have positive (n : ℕ) (hn : n ∈ C) : (μ n:ℝ)=1 := by
    obtain ⟨p,r,hp,hr,lt,rfl⟩ := RHTower.PrimeCells.squarefree_card_primeFactors_two_iff.mp (mem_filter.mp hn).2
    have cop := (Nat.coprime_primes hp hr).mpr lt.ne
    rw [isMultiplicative_moebius.map_mul_of_coprime cop,moebius_apply_prime hp,moebius_apply_prime hr]
    norm_num
  rw [same,sum_insert absent,sum_congr rfl positive,sum_const,nsmul_eq_mul,mul_one,moebius_apply_one,Int.cast_one]
  change 1+(C.card:ℝ)=(C.card:ℝ)+1
  exact add_comm ..

/-- In one density-one matching the fixed charge tracks the entire
semiprime population and the crossing charge carries its negative plus
the actual Mertens prefix. The two errors are opposite at every cutoff. -/
theorem opposite_charges_from_the_semiprime_population (w : ℕ → ℝ) (pos : ∀ n,0 ≤ w n)
    (top : Tendsto w atTop atTop) :
    ∃ G : ℕ → ℕ,Function.Involutive G ∧ (∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X) ∧
      ∀ X : ℕ,0<X →
        |fixedSignedPrefix G X-((squarefreeOmegaCount 2 X:ℝ)+1)| ≤ w X ∧
        crossingSignedPrefix G X-(coprimeMoebiusSum 1 X-((squarefreeOmegaCount 2 X:ℝ)+1))=
          -(fixedSignedPrefix G X-((squarefreeOmegaCount 2 X:ℝ)+1)) := by
  obtain ⟨G,back,legal,short,err⟩ := arbitrarily_slow_error_when_fixing_the_semiprimes w pos top
  refine ⟨G,back,legal,short,?_⟩
  intro X hx
  have count := (fixed_charge_error_le_support_errors G squarefreeSemiprimes X).trans (err X).1
  rw [signed_semiprime_target hx] at count
  have total := fixed_add_crossing G (fun n _ => ⟨back n,legal n⟩) X
  exact ⟨count,by linarith only [total]⟩

#print axioms opposite_charges_from_the_semiprime_population
#print axioms images_of_primes_force_distinct_support_errors
#print axioms unavoidable_errors_for_the_semiprime_support
#print axioms arbitrarily_slow_error_when_fixing_the_semiprimes

end GaloisForLFunctions.RestrictedFactorizationCalculus
