using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Assets.SAT
{
    /// <summary>
    /// Represents a SAT problem
    /// </summary>
    public class Problem
    {
        /// <summary>
        /// Make a problem from the constraints specified in the file
        /// The format of the file is:
        /// - 1 line per constraint
        /// - ! means not, | means or
        /// - proposition names can be anything not including those characters
        /// </summary>
        /// <param name="path">Path to the file to load</param>
        public Problem(string path)
        {
            Constraints.AddRange(File.ReadAllLines(path).Where(s => !s.StartsWith("#")).Select(constraintExp => Constraint.FromExpression(constraintExp, this)));
            TrueLiteralCounts = new int[Constraints.Count];
            
            Solution = new TruthAssignment(this);
            UnityEngine.Debug.Log($"Constraints.count: {Constraints.Count}");
            for (var i = 0; i < Constraints.Count; i++)
            {
                UnityEngine.Debug.Log($"Number of TrueLiteralCounts in Constraints {i}: {Solution.TrueLiteralCount(Constraints[i])}");
                TrueLiteralCounts[i] = Solution.TrueLiteralCount(Constraints[i]);
            }
            UnsatisfiedConstraints.AddRange(Constraints.Where(Unsatisfied));
        }
        
        /// <summary>
        /// The truth assignment we are trying to make into a solution.
        /// This starts completely random is then is gradually changed into
        /// a solution by "flipping" the values of specific propositions
        /// </summary>
        public TruthAssignment Solution;

        /// <summary>
        /// Percent of the time we do a random walk step rather than a greedy one.
        /// 0   = pure greedy
        /// 100 = pure random walk
        /// </summary>
        public int NoiseLevel = 10;

        #region Proposition information
        /// <summary>
        /// The Proposition object within this problem with the specified name.
        /// Creates a new proposition object if necessary.
        /// </summary>
        public Proposition this[string name]
        {
            get
            {
                if (propositionTable.TryGetValue(name, out var result))
                    return result;
                return propositionTable[name ] = new Proposition(name, propositionTable.Count);
            }
        }

        /// <summary>
        /// Hash table mapping names (string) to the Proposition objects with that name
        /// </summary>
        private readonly Dictionary<string, Proposition> propositionTable = new Dictionary<string, Proposition>();

        /// <summary>
        /// Enumeration of all the propositions in the problem
        /// </summary>
        public IEnumerable<Proposition> Propositions => propositionTable.Select(pair => pair.Value);

        /// <summary>
        /// Total number of propositions in the problem.
        /// Note this is the number of propositions, not the number of disjuncts in constraints.
        /// If a Proposition appears in 3 constraints, it's only counted once here.
        /// </summary>
        public int PropositionCount => propositionTable.Count;

        /// <summary>
        /// True if the current value of Solution is in fact a solution.
        /// If it's false, then we need to work on it some more.
        /// </summary>
        public bool IsSolved => UnsatisfiedConstraints.Count == 0;
        #endregion

        #region constraint information
        /// <summary>
        /// Constraints in the SAT problem.
        /// </summary>
        public readonly List<Constraint> Constraints = new List<Constraint>();

        /// <summary>
        /// List of constraints whose number of literals is not in its required range,
        /// i.e. MinTrueLiterals-MaxTrueLiterals.  The solver needs to get the number
        /// of true literals for each constraint into the right range.
        /// </summary>
        public readonly List<Constraint> UnsatisfiedConstraints = new List<Constraint>();

        /// <summary>
        /// Number of literals in each constraint that are true, indexed by the Index field of the constraint.
        /// So to find out how many literals are true in c, look at TrueLiteralCounts[c.Index].
        /// </summary>
        public int[] TrueLiteralCounts;

        /// <summary>
        /// Number of literals that are true within the constraint given the current TruthAssignment
        /// </summary>
        /// <param name="c"></param>
        /// <returns></returns>
        public int CurrentTrueLiterals(Constraint c) => TrueLiteralCounts[c.Index];

        /// <summary>
        /// True if the specified constraint is currently satisfied
        /// (i.e. if it's true in the current truth assignment)
        /// </summary>
        public bool Satisfied(Constraint c) => CurrentTrueLiterals(c) >= c.MinTrueLiterals && CurrentTrueLiterals(c) <= c.MaxTrueLiterals;

        /// <summary>
        /// True if the specified constraint is currently unsatisfied
        /// (i.e. false in the current truth assignment).
        /// </summary>
        public bool Unsatisfied(Constraint c) => !Satisfied(c);
        
        /// <summary>
        /// Checks that the TrueLiteralCounts array and UnsatisfiedConstraints list are correct.
        /// Use this to look for bugs in your implementation of Flip.
        /// </summary>
        public void CheckConsistency()
        {
            for (var i = 0; i < Constraints.Count; i++)
                if (TrueLiteralCounts[i] != Solution.TrueLiteralCount(Constraints[i]))
                    throw new Exception($"True literal count incorrect for constraint {i}");
            foreach (var c in Constraints)
            {
                var present = UnsatisfiedConstraints.IndexOf(c) >= 0;
                if (Satisfied(c))
                {
                    if (present)
                        throw new Exception($"constraint \"{c}\" appears in UnsatisfiedConstraints but is satisfied.  Last flip was {lastFlip}");
                }
                else if (!present)
                    throw new Exception($"constraint \"{c}\" is unsatisfied but does not appear in the UnsatisfiedConstraints list.  Last flip was {lastFlip}");
            }
        }
        #endregion

        #region Solver
        /// <summary>
        /// Pick one variable to flip and flip it by calling Flip, below.
        /// </summary>
        /// <returns>True if all constraints are satisfied.</returns>
        public bool StepOne()
        {
            // TODO: Fill this in!
            UnityEngine.Debug.Log("StepOne function:");
            UnityEngine.Debug.Log($"number of UnsatisfiedConstraints: {UnsatisfiedConstraints.Count}");
            var random_constraint = Random.RandomElement(UnsatisfiedConstraints);
            var c = UnsatisfiedConstraints.RandomElement();
            var random_literal = random_constraint.RandomLiteral;

            
            if (!Random.Percent(NoiseLevel))
            {
                var currentBest = random_constraint.Literals[0];
                foreach (var current_literal in random_constraint.Literals)
                {
                    if (SatisfiedConstraintDelta(current_literal.Proposition) > SatisfiedConstraintDelta(currentBest.Proposition))
                    {
                        currentBest = current_literal;
                    }
                }

                random_literal = currentBest;

                bool increased_flag = false;
                var oldConstraint = SatisfiedConstraintDelta(lastFlip.Proposition);
                var newConstraint = SatisfiedConstraintDelta(currentBest.Proposition);
                if (lastFlip != null && oldConstraint < newConstraint)
                {
                    increased_flag = true;
                }

                if (increased_flag == true)
                {
                    if (NoiseLevel > 0)
                    {
                        NoiseLevel-=1;
                    }
                }
                else
                {
                    if (NoiseLevel < 100)
                    {
                        NoiseLevel+=1;
                    }
                }
            }
            Flip(random_literal);
            return UnsatisfiedConstraints.Count == 0;
        }



        private Literal lastFlip;
        /// <summary>
        /// Flip the value of the specified literal.
        /// Call Solution.Flip to do the actual flipping.  But make sure to update
        /// TrueLiteralCounts and UnsatisfiedConstraints, accordingly
        /// </summary>
        void Flip(Literal l)
        {
            lastFlip = l;
            var p = l.Proposition;
            var old = Solution[p];
            UnityEngine.Debug.Log($"{p.Name}: {old}->{!old}");
            Solution.Flip(p);

            // TODO: Fill this in!
            // look at positiveConstraints and negativecConstraints fields of the proposition you're flipping on
            // make sure you correctly update the TrueLiteralCounts and UnsatisfiedConstraints tables

            //p.PositiveConstraints is LIST OF CONSTRAINTS proposition p appears in Positive form
            UnityEngine.Debug.Log($"Proposition {p.Name} appears in different Positiveform clauses: {p.PositiveConstraints.Count} times.");

            if (Solution[p]) //if proposition changed from F to T
            {
                //update PositiveConstraints' list of constraints
                foreach (var c in p.PositiveConstraints) // iterate thru the list of positive constraints
                {
                    var oldTrueCount = TrueLiteralCounts[c.Index];
                    TrueLiteralCounts[c.Index] += 1;
                    UnityEngine.Debug.Log($"Constraint{c.Index}: {oldTrueCount}-->{TrueLiteralCounts[c.Index]}");
                }

                foreach (var c in p.NegativeConstraints)
                {
                    var oldTrueCount = TrueLiteralCounts[c.Index];
                    TrueLiteralCounts[c.Index] -= 1;
                    UnityEngine.Debug.Log($"Constraint{c.Index}: {oldTrueCount}-->{TrueLiteralCounts[c.Index]}");
                }
            }

            else //if proposition changed from T to F

            {
                UnityEngine.Debug.Log($"Proposition {p.Name} appears in different Negativeform clauses: {p.PositiveConstraints.Count} times.");
                //update PositiveConstraints' list of constraints
                foreach (var c in p.PositiveConstraints) // iterate thru the list of positive constraints
                {
                    var oldTrueCount = TrueLiteralCounts[c.Index];
                    TrueLiteralCounts[c.Index] -= 1;
                    UnityEngine.Debug.Log($"Constraint{c.Index}: {oldTrueCount}-->{TrueLiteralCounts[c.Index]}");
                }

                foreach (var c in p.NegativeConstraints)
                {
                    var oldTrueCount = TrueLiteralCounts[c.Index];
                    TrueLiteralCounts[c.Index] += 1;
                    UnityEngine.Debug.Log($"Constraint{c.Index}: {oldTrueCount}-->{TrueLiteralCounts[c.Index]}");
                }
            }
            foreach (var c in Constraints)
            {
                if (Satisfied(c))
                {
                    if (UnsatisfiedConstraints.Contains(c))
                    {
                        UnsatisfiedConstraints.Remove(c);
                    }
                }
                else
                {
                    if (!UnsatisfiedConstraints.Contains(c))
                    {
                        UnsatisfiedConstraints.Add(c);
                    }
                }
            }
        }

        /// <summary>
        /// Return the net increase or decrease in satisfied constraints if we were to flip this proposition
        /// </summary>
        int SatisfiedConstraintDelta(Proposition p)
        {

            // TODO: Fill this in!
            
            UnityEngine.Debug.Log($"Current number of UnsatisfiedConstraints: {UnsatisfiedConstraints.Count}");
            UnityEngine.Debug.Log($"If we were to flip this proposition {p}...");
            var oldCount = UnsatisfiedConstraints.Count;
            Solution.Flip(p);
            if (Solution[p])
            {
                foreach (var c in p.PositiveConstraints)
                {
                    TrueLiteralCounts[c.Index] += 1;
                }
                foreach (var c in p.NegativeConstraints)
                {
                    TrueLiteralCounts[c.Index] -= 1;
                }
            }
            else
            {
                foreach (var c in p.PositiveConstraints)
                {
                    TrueLiteralCounts[c.Index] -= 1;
                }
                foreach (var c in p.NegativeConstraints)
                {
                    TrueLiteralCounts[c.Index] += 1;
                }
            }

            foreach (var c in Constraints)
            {
                if (Satisfied(c))
                {
                    if (UnsatisfiedConstraints.Contains(c))
                    {
                        UnsatisfiedConstraints.Remove(c);
                    }
                }
                else
                {
                    if (!UnsatisfiedConstraints.Contains(c))
                    {
                        UnsatisfiedConstraints.Add(c);
                    }
                }
            }
            var newCount = UnsatisfiedConstraints.Count;
            var netDiff = oldCount - newCount;
            Solution.Flip(p);
            if (Solution[p])
            {
                foreach (var c in p.PositiveConstraints)
                {
                    TrueLiteralCounts[c.Index] += 1;
                }
                foreach (var c in p.NegativeConstraints)
                {
                    TrueLiteralCounts[c.Index] -= 1;
                }
            }
            else
            {
                foreach (var c in p.PositiveConstraints)
                {
                    TrueLiteralCounts[c.Index] -= 1;
                }
                foreach (var c in p.NegativeConstraints)
                {
                    TrueLiteralCounts[c.Index] += 1;
                }
            }

            foreach (var c in Constraints)
            {
                if (Satisfied(c))
                {
                    if (UnsatisfiedConstraints.Contains(c))
                    {
                        UnsatisfiedConstraints.Remove(c);
                    }
                }
                else
                {
                    if (!UnsatisfiedConstraints.Contains(c))
                    {
                        UnsatisfiedConstraints.Add(c);
                    }
                }
            }

            return netDiff;
        }
        #endregion
    }
}
