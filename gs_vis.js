const stage = new Stage()

// Fetch proposers and receivers dynamically
const proposers = instance.signature('Proposer').atoms();
const receivers = instance.signature('Receiver').atoms();

// Fetch fields dynamically
const matchField = instance.signature('Person').field('match');
const pPrefField = instance.signature('Proposer').field('p_preferences');
const rPrefField = instance.signature('Receiver').field('r_preferences');

// Helper: get matches
const matches = {};
proposers.forEach(proposer => {
  const matched = matchField.projections[proposer.id];
  if (matched && matched.length > 0) {
    matches[proposer.id] = matched[0].id; // map proposer id -> receiver id
  }
});

// Helper: build proposer preference lists
const pPreferences = {};
proposers.forEach(proposer => {
  const prefs = [];
  const prefsForProposer = pPrefField.projections[proposer.id] || {};
  Object.keys(prefsForProposer).forEach(receiverId => {
    prefs.push({receiver: receiverId, score: prefsForProposer[receiverId][0].id});
  });
  // Sort descending by score
  prefs.sort((a,b) => parseInt(b.score) - parseInt(a.score));
  pPreferences[proposer.id] = prefs;
});

// Helper: build receiver preference lists
const rPreferences = {};
receivers.forEach(receiver => {
  const prefs = [];
  const prefsForReceiver = rPrefField.projections[receiver.id] || {};
  Object.keys(prefsForReceiver).forEach(proposerId => {
    prefs.push({proposer: proposerId, score: prefsForReceiver[proposerId][0].id});
  });
  // Sort descending by score
  prefs.sort((a,b) => parseInt(b.score) - parseInt(a.score));
  rPreferences[receiver.id] = prefs;
});

// Layout constants
const startX = 100;
const pPrefX = startX;
const proposerX = pPrefX + 150;
const receiverX = proposerX + 250;
const rPrefX = receiverX + 150;
const startY = 100;
const spacingY = 150;

// Map from ID to label for nicer display
function shortName(atom) {
  return atom.replace(/^this\/|^\$|\//g, '');
}

// Draw proposer preferences
proposers.forEach((proposer, i) => {
  const prefs = pPreferences[proposer.id].map((p, idx) => {
    const marker = matches[proposer.id] === p.receiver ? '> ' : '';
    return `${marker}${idx+1}. ${shortName(p.receiver)} (${shortName(p.score)})`;
  }).join('\n');

  stage.add(new TextBox({
    text: prefs,
    coords: {x: pPrefX, y: startY + i * spacingY},
    color: 'black',
    fontSize: 12
  }));
});

// Draw proposers
proposers.forEach((proposer, i) => {
  stage.add(new TextBox({
    text: shortName(proposer.id),
    coords: {x: proposerX, y: startY + i * spacingY},
    color: 'blue',
    fontSize: 16
  }));
});

// Draw receivers
receivers.forEach((receiver, i) => {
  stage.add(new TextBox({
    text: shortName(receiver.id),
    coords: {x: receiverX, y: startY + i * spacingY},
    color: 'green',
    fontSize: 16
  }));
});

// Draw receiver preferences
receivers.forEach((receiver, i) => {
  const prefs = rPreferences[receiver.id].map((p, idx) => {
    // Find the matched proposer for this receiver
    const matchedProposer = Object.keys(matches).find(pid => matches[pid] === receiver.id);
    const marker = matchedProposer === p.proposer ? '> ' : '';
    return `${marker}${idx+1}. ${shortName(p.proposer)} (${shortName(p.score)})`;
  }).join('\n');

  stage.add(new TextBox({
    text: prefs,
    coords: {x: rPrefX, y: startY + i * spacingY},
    color: 'black',
    fontSize: 12
  }));
});

// Draw arrows
proposers.forEach((proposer, i) => {
  const receiverId = matches[proposer.id];
  const receiverIndex = receivers.findIndex(r => r.id === receiverId);

  if (receiverIndex >= 0) {
    stage.add(new Arrow({
      start: {x: proposerX + 70, y: startY + i * spacingY + 10},
      end: {x: receiverX - 10, y: startY + receiverIndex * spacingY + 10},
      twoSided: true,
      color: 'black'
    }));
  }
});

stage.render(svg, document);
