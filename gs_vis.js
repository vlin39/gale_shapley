const stage = new Stage()
const inst = instances[2]
const proposerAtoms = inst.signature('Proposer').atoms()
const receiverAtoms = inst.signature('Receiver').atoms()
const matchTuples = inst.field('match').tuples()

let proposerGrid = new Grid({
    grid_location: {x: 50, y:50},
    cell_size: {x_size: 120, y_size: 60},
    grid_dimensions: {x_size: 1, y_size: proposerAtoms.length}
})
stage.add(proposerGrid)

let receiverGrid = new Grid({
    grid_location: {x: 300, y:50},
    cell_size: {x_size: 120, y_size: 60},
    grid_dimensions: {x_size: 1, y_size: receiverAtoms.length}
})
stage.add(receiverGrid)

const mapping = {}

for(const [idx, p] of proposerAtoms.entries()) {
    const prect = new Rectangle(
        {label: `${p.id()}`, 
        coords: {x:100,y:100}, 
        color: 'lightsteelblue', 
        borderColor: 'black',
        borderWidth: 2,
        width: 100, 
        height: 50})
    mapping[p.id()] = prect
    receiverGrid.add({x: 0, y: idx}, prect)
}

for(const [idx, r] of receiverAtoms.entries()) {
    const rrect = new Rectangle(
        {label: `${r.id()}`, 
        coords: {x:100,y:100}, 
        color: 'lightgreen', 
        borderColor: 'black',
        borderWidth: 2,
        width: 100, 
        height: 50})
    mapping[r.id()] = rrect
    proposerGrid.add({x: 0, y: idx}, rrect)
}

proposerGrid.hide_grid_lines()
receiverGrid.hide_grid_lines()

console.log(mapping)

for(const tup of matchTuples) {
    const first = tup.atoms()[0].id()
    const second = tup.atoms()[1].id()
    console.log(first)
    console.log(second)
    
    const e = new Edge({
        obj1: mapping[first], obj2: mapping[second],
        textProps: {text: "match", fontSize: 11},
        textLocation: "above"
    })    
    stage.add(e)
}

stage.render(svg, document)
