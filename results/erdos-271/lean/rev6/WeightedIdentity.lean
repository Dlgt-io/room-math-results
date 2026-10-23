import JCounting
import PairLedger

noncomputable section
namespace Erdos271.FiniteIntegrals

def upperIndicator (p t : Real) : Real :=
  Set.indicator (Set.Ici p) (Function.const Real (1 : Real)) t

def positiveCount (P : Finset Real) (t : Real) : Real :=
  P.sum (fun p => upperIndicator p t)

def squareIntegrand (P : Finset Real) (t : Real) : Real :=
  positiveCount P t ^ 2 / t ^ 2

def doubleIntegrand (P : Finset Real) (t : Real) : Real :=
  intervalIntegral
    (fun u => positiveCount P u * positiveCount P t / (2 * t - u) ^ 3)
    0 t MeasureTheory.volume

def squareIntegral (P : Finset Real) (X : Real) : Real :=
  intervalIntegral (squareIntegrand P) 0 X MeasureTheory.volume

def doubleIntegral (P : Finset Real) (X : Real) : Real :=
  intervalIntegral (doubleIntegrand P) 0 X MeasureTheory.volume

def forwardPairWeight (p q : Real) : Real :=
  if p < q then 1 / (2 * q - p) else 0

def weightedPairs (P : Finset Real) : Real :=
  P.sum (fun p => 1 / (2 * p)) +
    P.sum (fun p => P.sum (fun q => forwardPairWeight p q))

def boundaryTerm (P : Finset Real) (X : Real) : Real :=
  (P.card : Real) * P.sum (fun p => 1 / (2 * X - p)) -
    (P.card : Real) ^ 2 / (2 * X)

theorem finite_weighted_integral_identity
    (P : Finset Real) (X : Real) (hX : 0 < X)
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ X) :
    IntervalIntegrable (squareIntegrand P) MeasureTheory.volume 0 X ∧
    IntervalIntegrable (doubleIntegrand P) MeasureTheory.volume 0 X ∧
    weightedPairs P = (3 / 2) * squareIntegral P X -
      4 * doubleIntegral P X + boundaryTerm P X ∧
    0 ≤ boundaryTerm P X ∧
    boundaryTerm P X ≤ (P.card : Real) ^ 2 / (2 * X) := by
  classical
  let ip : Real → Real → Real := fun p q => 1 / max p q - 1 / X
  let jp : Real → Real → Real := fun p q =>
    1 / (2 * max p q) - 1 / (2 * X) +
      1 / (4 * (2 * X - p)) - 1 / (4 * (2 * max p q - p))
  have hi := counting_square_integral P X upperIndicator (positiveCount P)
    (squareIntegrand P) ip hX hP (fun p => rfl) (fun t => rfl)
    (fun t => rfl) (fun p q => rfl)
  have hj := counting_double_integral P X upperIndicator (positiveCount P)
    (fun t u => positiveCount P u * positiveCount P t / (2 * t - u) ^ 3)
    (doubleIntegrand P) jp hX hP (fun p => rfl) (fun t => rfl)
    (fun t u => rfl) (fun t => rfl) (fun p q => rfl)
  have hw := finite_pair_ledger P X ip jp
    (fun p => 1 / (2 * X - p)) (fun p => 1 / (2 * p)) forwardPairWeight
    hX hP (fun p q => rfl) (fun p q => rfl)
    (fun p => rfl) (fun p => rfl) (fun p q => rfl)
  refine ⟨hi.1, hj.1, ?_, hw.2.1, hw.2.2⟩
  dsimp only [squareIntegral, doubleIntegral]
  rw [hi.2, hj.2]
  exact hw.1

end Erdos271.FiniteIntegrals
